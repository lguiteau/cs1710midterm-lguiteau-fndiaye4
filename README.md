# cs1710midterm-lguiteau-fndiaye4
CS1710 Midterm

# Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

For our model, we decided to model a spanning tree of weather stations. The weather stations were represented by nodes and the edges between them represented a direct link of communication. Our goal was to do this without cycles but all nodes being connected. Our scope for this project was for the stations to be able to communicate with each other about if a storm was coming or not. The root or central station would be the only node to  receive the information directly about the storm prediction and then that information would propagate from parent to child. In the end our goal was for every station to eventually receive the same information. My partner and I found this idea interesting because one partner loves weather and weather modeling and the other has an interest in entrepreneurship and business. Weather station communication is very important because it can save lives to propagate storm information to help prepare for destruction and evacuate. Also from an entrepreneurship perspective, having all the information propagated through the parents to child instead of all of them being connected to the central hub for information is more efficient and cost effective by reducing redundancy.

# Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

