block_cipher = None
a = Analysis(
    ['app.py'],
    pathex=['.'],
    binaries=[
        ('bin/yt-dlp', '.'),
        ('bin/ffmpeg', '.'),
    ],
    datas=[],
    hiddenimports=['rumps', 'flask', 'werkzeug'],
    cipher=block_cipher,
)
pyz = PYZ(a.pure, a.zipped_data, cipher=block_cipher)
exe = EXE(pyz, a.scripts, [], exclude_binaries=True,
          name='+downloads', debug=False, strip=False,
          upx=False, console=False)
coll = COLLECT(exe, a.binaries, a.zipfiles, a.datas,
               strip=False, upx=False, name='+downloads')
app = BUNDLE(coll,
             name='+downloads.app',
             icon='icon.icns',
             bundle_identifier='com.jaysperspective.downloads',
             info_plist={
                 'CFBundleShortVersionString': '1.3',
             })
