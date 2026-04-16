FROM python:3.12-slim
RUN apt-get update && apt-get install -y ffmpeg curl nodejs && \
    curl -L https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp \
         -o /usr/local/bin/yt-dlp && chmod +x /usr/local/bin/yt-dlp
WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt
COPY app.py .
COPY static/ static/
ENV DOWNLOAD_DIR=/data/downloads
VOLUME ["/data"]
EXPOSE 5055
CMD ["gunicorn", "-w", "1", "--threads", "8", "-b", "0.0.0.0:5055", "--timeout", "300", "app:app"]
