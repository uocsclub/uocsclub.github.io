# Contributing

Much like the rest of UOCSClub activities, our website strongly relies on the
creative efforts of its members. We ask that if you are a member of our
club, and you would like to contribute to our site, to read the following
and send us your pull request.

## Basic Instructions

Step one, fork our repo.

Step two, clone the forked repo.

```
git clone git@github.com:<you-username>/uocsclub.github.io
```

Step three, check out our
[issues page](https://github.com/uocsclub/uocsclub.github.io/issues) for an
open issue that you can help with.

Step four, do your thing.

Step five, push your changes and send us a pull request.

## Guidelines

Keep the site static. Little to no JavaScript is preferred.

When creating a new page, please use the following when adding files.

- HTML file `/<page name>.html`
- CSS file `/css/<page name>.html`
- Images files `/images/<page name>/<image name>`
- JS files (if needed) `/js/<page name>.js`

If you are making a new core page of our site (like a Contact Us, Events,
Calender, Join, etc.) then remember to add the main pages navbar.

More guidelines will become available once we have setup our templating
engine.

## Testing Your Site Locally

Currently, our site is just basic http server. As long as your computer
can run a web server, you can test the site. Here are a few examples.

If you have Python 3

```bash
cd uocsclub.github.io
python -m http.server 8000
```

If you have Python 2

```bash
cd uocsclub.github.io
python -m SimpleHTTPServer 8000
```

Then check out your [local server](http://localhost:8000).

We may switch to using a templating engine for our site, if needed. When
we do, we will update this page.
