# Proof audit

Run the complete build and elaborated-environment audit with:

```sh
lake build
lake env lean Audit/ProjectDeclarations.lean
lake env lean Audit/FoundationalAxioms.lean
```

`ProjectDeclarations.lean` inspects every declaration whose name begins with
`StressTensor` in Lean's elaborated environment. It fails if it finds a custom
`axiom`/`constant` declaration or a dependency on `sorryAx`. At delivery time
it checked 606 declarations and reported no project-defined axioms or proof
placeholders.

“No project-defined axioms” should not be confused with a literally empty
output from Lean's `#print axioms`. The analysis library uses Lean's standard
logical principles `propext`, `Classical.choice`, and `Quot.sound`; the
representative theorem audit records exactly those three. No mathematical
claim specific to this project is introduced through an axiom declaration.

The structures `CKOutcome`, `SectionFourEndpointData`, and `RelaxationBridge`
are explicit interfaces. A theorem using one must receive a value of that
structure, so their assumptions remain visible in theorem signatures. In
particular, `RelaxationBridge` is not a formal proof of the cited BV relaxation
theorem; it is the typed boundary at which that theorem must eventually be
implemented.
