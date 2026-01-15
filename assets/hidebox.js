var coll = document.getElementsByClassName("collapsible");
var i;

for (i = 0; i < coll.length; i++) {
	coll[i].addEventListener("click", function() {

		this.classList.toggle("active");

		var content = this.parentElement.parentElement.nextElementSibling;

		if (content.style.display === "block") {
			content.style.display = "none";
			this.innerText = "[show]";
		} else {
			content.style.display = "block";
			this.innerText = "[hide]";
		}

	});
}