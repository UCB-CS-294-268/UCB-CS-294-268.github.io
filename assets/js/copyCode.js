document.addEventListener('DOMContentLoaded', () => {
  // Define SVG icons
  const copyIconSvg = `
    <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
      <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
      <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path>
    </svg>
  `;

  const checkIconSvg = `
    <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
      <polyline points="20 6 9 17 4 12"></polyline>
    </svg>
  `;

  document.querySelectorAll('pre.highlight').forEach((codeBlock) => {
    const button = document.createElement('button');
    button.className = 'copy-code-button';
    button.type = 'button';
    button.setAttribute('aria-label', 'Copy code to clipboard');
    button.innerHTML = copyIconSvg; // Insert the copy icon

    button.addEventListener('click', () => {
      const code = codeBlock.querySelector('code').innerText;
      
      navigator.clipboard.writeText(code).then(() => {
        // Success feedback
        button.innerHTML = checkIconSvg; // Change to check icon
        button.classList.add('copied');  // Apply the green color class

        // Revert back after 2 seconds
        setTimeout(() => {
          button.innerHTML = copyIconSvg;
          button.classList.remove('copied');
        }, 2000);
      });
    });

    codeBlock.appendChild(button);
  });
});
