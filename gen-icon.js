// gen-icon.js: generate a program icon for nncmpp as an Apple iconset
//
// Copyright (c) 2026, Přemysl Eric Janouch <p@janouch.name>
// SPDX-License-Identifier: 0BSD
//
// API documentation: https://manicmaniac.github.io/sips-js-api/modules.html

// Apple uses something close to a "quintic superellipse" in their icons,
// but doesn't quite match. Either way, it looks better than rounded rectangles.
function addSquircle(canvas, bounds) {
	const midX = bounds.x + bounds.width / 2
	const midY = bounds.y + bounds.height / 2
	canvas.moveTo(bounds.x + bounds.width, midY)
	for (let theta = 0; theta < Math.PI * 2; theta += Math.PI / 1e4) {
		const x = Math.pow(Math.abs(Math.cos(theta)), 2 / 5) * bounds.width / 2
			* Math.sign(Math.cos(theta)) + midX
		const y = Math.pow(Math.abs(Math.sin(theta)), 2 / 5) * bounds.height / 2
			* Math.sign(Math.sin(theta)) + midY
		canvas.lineTo(x, y)
	}
	canvas.closePath()
}

function drawIcon(size) {
	const canvas = new Canvas(size, size)
	const nominal = 1024
	const scale = size / nominal

	// Drawing in the Postscript coordinate system.
	canvas.translate(0, size)
	canvas.scale(scale, -scale)

	const bounds = new Rect(100, 100, nominal - 200, nominal - 200)

	canvas.save()
	canvas.beginPath()
	addSquircle(canvas, bounds)
	canvas.shadowOffsetX = 0
	canvas.shadowOffsetY = -12 * scale
	canvas.shadowBlur = 28 * scale
	canvas.shadowColor = 'rgba(0, 0, 0, 0.375)'
	canvas.fillStyle = '#d8d8d8'
	canvas.fill()
	canvas.restore()

	canvas.save()
	canvas.beginPath()
	addSquircle(canvas, bounds)
	canvas.clip()
	const gradient = canvas.createLinearGradient(0, 100, 0, nominal - 100)
	gradient.addColorStop(0, '#cccccc')
	gradient.addColorStop(1, '#ffffff')
	canvas.fillStyle = gradient
	canvas.fillRect(0, 0, nominal, nominal)
	canvas.restore()

	// The same shape as in nncmpp.svg.
	canvas.beginPath()
	canvas.moveTo(nominal * 0.325, nominal * 0.30)
	canvas.lineTo(nominal * 0.325, nominal * 0.70)
	canvas.lineTo(nominal * 0.725, nominal * 0.50)
	canvas.closePath()
	canvas.fillStyle = '#000'
	canvas.fill()

	return canvas
}

// Beware, this is most likely going to be generated in the Display P3 profile,
// and I haven't found a way to change this.
for (const size of [16, 32, 128, 256, 512]) {
	new Output(drawIcon(size), `icon_${size}x${size}.png`).addToQueue()
	new Output(drawIcon(size * 2), `icon_${size}x${size}@2x.png`).addToQueue()
}
