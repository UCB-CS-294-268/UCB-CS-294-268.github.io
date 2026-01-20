document.addEventListener("DOMContentLoaded", function() {
  const container = document.querySelector('.post-content'); 
  if (!container) return;

  // --- 1. Create the "Collapse All" Button ---
  const toggleAllBtn = document.createElement('button');
  toggleAllBtn.id = 'global-toggle-btn';
  toggleAllBtn.innerText = "Collapse All"; 
  
  // Style the button directly (or move to CSS)
  toggleAllBtn.style.marginBottom = "20px";
  toggleAllBtn.style.padding = "8px 15px";
  toggleAllBtn.style.cursor = "pointer";

  // --- 2. Insert Button after TOC ---
  // We look for the standard Jekyll/Kramdown TOC ID ('#markdown-toc')
  // If your theme uses a different class for the TOC (like '.toc'), change the selector below.
  const toc = document.querySelector('#markdown-toc'); 
  
  if (toc) {
    toc.insertAdjacentElement('afterend', toggleAllBtn);
  } else {
    // Fallback: If no TOC is found, put it at the very top
    container.insertBefore(toggleAllBtn, container.firstChild);
  }

  // --- 3. Wrap Content (H2 ONLY) ---
  const headers = container.querySelectorAll('h2');

  headers.forEach(header => {
    const wrapper = document.createElement('div');
    wrapper.className = 'section-content';
    // CHANGE 1: Set default to 'block' (visible) instead of 'none'
    wrapper.style.display = 'block'; 

    let nextNode = header.nextElementSibling;
    const nodesToWrap = [];

    while (nextNode && nextNode.tagName !== 'H2') {
      nodesToWrap.push(nextNode);
      nextNode = nextNode.nextElementSibling;
    }

    nodesToWrap.forEach(node => wrapper.appendChild(node));
    header.parentNode.insertBefore(wrapper, header.nextSibling);

    header.style.cursor = 'pointer';
    header.classList.add('collapsible-header');
    
    // CHANGE 2: Default arrow points UP (indicating it is open)
    header.innerHTML += ' <span class="toggle-icon" style="font-size:0.7em; float:right">▲</span>';

    header.addEventListener('click', () => {
      const isVisible = wrapper.style.display === 'block';
      wrapper.style.display = isVisible ? 'none' : 'block';
      
      // Update arrow
      const arrow = header.querySelector('.toggle-icon');
      arrow.innerHTML = isVisible ? '▼' : '▲';
    });
  });

  // --- 4. Global Collapse/Expand Button Logic ---
  toggleAllBtn.addEventListener('click', () => {
    const isCollapsing = toggleAllBtn.innerText === "Collapse All";
    
    document.querySelectorAll('.section-content').forEach(w => {
        w.style.display = isCollapsing ? 'none' : 'block';
    });
    
    document.querySelectorAll('.toggle-icon').forEach(icon => {
        icon.innerHTML = isCollapsing ? '▼' : '▲';
    });

    toggleAllBtn.innerText = isCollapsing ? "Expand All" : "Collapse All";
  });

  // --- 5. TOC Link Handler (Auto-open) ---
  // This function opens the section if a user clicks a TOC link pointing to hidden content
  function handleHashLocation() {
    const hash = window.location.hash;
    if (hash) {
      // Find the element the link points to (e.g., #subsection-1)
      const targetElement = document.querySelector(hash);
      
      if (targetElement) {
        // Find if this element is inside a hidden .section-content wrapper
        const wrapper = targetElement.closest('.section-content');
        
        // If it is inside a wrapper and that wrapper is hidden...
        if (wrapper && wrapper.style.display === 'none') {
          // 1. Reveal the section
          wrapper.style.display = 'block';
          
          // 2. Update the arrow on the corresponding H2 header
          // We find the H2 that comes immediately before this wrapper
          const previousH2 = wrapper.previousElementSibling;
          if (previousH2 && previousH2.tagName === 'H2') {
             const arrow = previousH2.querySelector('.toggle-icon');
             if(arrow) arrow.innerHTML = '▲';
          }
        }
        
        // 3. Scroll to the element (give browser a moment to render the layout change)
        setTimeout(() => {
          targetElement.scrollIntoView({ behavior: 'smooth' });
        }, 100);
      }
    }
  }

  // Listen for hash changes (clicking TOC links)
  window.addEventListener('hashchange', handleHashLocation);
  
  // Check hash on initial page load (e.g. sharing a direct link)
  handleHashLocation();
});
