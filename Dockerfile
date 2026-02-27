FROM python:3.12-slim
RUN apt-get update && apt-get install -y ffmpeg curl && \
    curl -L https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp \
         -o /usr/local/bin/yt-dlp && chmod +x /usr/local/bin/yt-dlp
WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt
COPY app.py .
ENV DOWNLOAD_DIR=/data/downloads
VOLUME ["/data"]
EXPOSE 5055
CMD ["python", "app.py"]
