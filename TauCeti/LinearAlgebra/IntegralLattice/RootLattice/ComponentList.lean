/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
-- The discriminant quadratic module of an orthogonal sum is the orthogonal product of the
-- component discriminant quadratic modules, the induction step of the list construction.
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Basic
-- Each component's glue alphabet, with its isometry to the discriminant form of the component's
-- root lattice.

/-!
# Glue words for an ordered list of ADE components

Conway--Sloane record a glue vector of a reducible root system by one label per component, in the
displayed component order, and report the discriminant form of the component sum in those
coordinates.  This file builds that coordinate language for an arbitrary ordered list of ADE
components, uniformly in the components and without a case split on the individual types.

An ADE component is `TauCeti.DynkinType.Component`, a valid simply-laced Dynkin type.  For a list
`l` of components:

* `TauCeti.DynkinType.componentAlphabet l` is the dependent coordinate product of the component
  glue alphabets `TauCeti.DynkinType.Component.glueAlphabet`, so that a glue word carries one label
  per component, each drawn from that component's own alphabet.  In particular the `Dₙ` factor is
  the parity-dependent alphabet of `TauCeti.DynkinType.glueAlphabet`, not a single cyclic group.
* `TauCeti.DynkinType.componentSumLattice l` is the orthogonal sum of the component root lattices,
  nested to the right, with the zero lattice for the empty list.  It is even and nondegenerate.
* `TauCeti.DynkinType.componentDiscriminantIsometry l` is the induced isometry from the glue
  alphabet of `l` to the discriminant quadratic module of `componentSumLattice l`.  It is built by
  induction out of the component isometries and the orthogonal-sum discriminant equivalence, and
  its value on a glue word is recorded by `componentDiscriminantIsometry_cons`.
* A componentwise isometry of the component lists induces an isometry of the glue alphabets and an
  isometry of the component sums, and the component-list discriminant isometry intertwines them
  (`componentDiscriminantIsometry_natural`).

## Main declarations

* `TauCeti.DynkinType.Component`: an ADE component, with its root lattice and glue alphabet.
* `TauCeti.DynkinType.componentAlphabet`: the glue alphabet of an ordered component list.
* `TauCeti.DynkinType.componentSumLattice`: the orthogonal sum of the component root lattices.
* `TauCeti.DynkinType.componentDiscriminantIsometry`: the induced isometry of discriminant forms.
* `TauCeti.DynkinType.ComponentIsometry`, `componentSumIsometry`, `componentAlphabetIsometry`:
  componentwise isometries of two component lists and their two induced isometries.
* `TauCeti.DynkinType.Component.glueAlphabetIsometry_apply`, `componentSumIsometry_nil`,
  `componentSumIsometry_cons`, `componentAlphabetIsometry_cons`,
  `glueAlphabetIsometry_componentGlueAlphabetIsometry`: the evaluation laws that characterise these
  isometries on glue labels and on component vectors, so that downstream proofs do not unfold their
  constructions.
* `TauCeti.DynkinType.componentDiscriminantIsometry_natural`: naturality of the component-list
  discriminant isometry under those componentwise isometries.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3, and
  Chapter 16, §1.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

/-- An ADE component: a valid simply-laced Dynkin type.  A reducible root system is an ordered
finite list of components. -/
abbrev Component : Type := {t : DynkinType // t.Valid ∧ t.IsSimplyLaced}

namespace Component

/-- The rank of a component, the number of simple roots. -/
@[expose] def rank (c : Component) : ℕ := c.1.rank

/-- The positive root lattice of a component, on its simple-root coordinate space. -/
@[expose] noncomputable def rootLattice (c : Component) : IntegralLattice (Fin c.rank → ℚ) :=
  c.1.rootLattice c.2.2

/-- The root lattice of a component is even. -/
theorem isEven_rootLattice (c : Component) : c.rootLattice.IsEven :=
  c.1.isEven_rootLattice c.2.2

/-- The root lattice of a component is nondegenerate. -/
instance isNondegenerate_rootLattice (c : Component) : c.rootLattice.IsNondegenerate :=
  inferInstanceAs (c.1.rootLattice c.2.2).IsNondegenerate

/-- The glue alphabet of a component: the finite quadratic module of its glue labels. -/
@[expose] noncomputable def glueAlphabet (c : Component) : FiniteQuadraticModule :=
  c.1.glueAlphabet c.2.2

/-- The glue alphabet of a component is the discriminant quadratic module of its root lattice. -/
noncomputable def glueAlphabetIsometry (c : Component) :
    FiniteQuadraticModule.Isometry c.glueAlphabet
      (c.rootLattice.discriminantQuadraticModule c.isEven_rootLattice) :=
  c.1.glueAlphabetIsometry c.2.1 c.2.2

/-- The glue isometry of a component acts as the glue isometry of its underlying Dynkin type. -/
@[simp]
theorem glueAlphabetIsometry_apply (c : Component) (x : c.glueAlphabet) :
    c.glueAlphabetIsometry x = c.1.glueAlphabetIsometry c.2.1 c.2.2 x :=
  (rfl)

end Component

/-- The ambient coordinate space of the orthogonal sum of an ordered component list: the product of
the component simple-root coordinate spaces, nested to the right. -/
@[expose] def componentSumAmbient : List Component → Type
  | [] => Fin 0 → ℚ
  | c :: cs => (Fin c.rank → ℚ) × componentSumAmbient cs

@[reducible] instance instAddCommGroupComponentSumAmbient : (l : List Component) →
    AddCommGroup (componentSumAmbient l)
  | [] => inferInstanceAs (AddCommGroup (Fin 0 → ℚ))
  | c :: cs =>
    letI : AddCommGroup (componentSumAmbient cs) := instAddCommGroupComponentSumAmbient cs
    inferInstanceAs (AddCommGroup ((Fin c.rank → ℚ) × componentSumAmbient cs))

@[reducible] instance instModuleComponentSumAmbient : (l : List Component) →
    Module ℚ (componentSumAmbient l)
  | [] => inferInstanceAs (Module ℚ (Fin 0 → ℚ))
  | c :: cs =>
    letI : AddCommGroup (componentSumAmbient cs) := instAddCommGroupComponentSumAmbient cs
    letI : Module ℚ (componentSumAmbient cs) := instModuleComponentSumAmbient cs
    inferInstanceAs (Module ℚ ((Fin c.rank → ℚ) × componentSumAmbient cs))

/-- The empty coordinate space is a subsingleton, so the empty component sum has one vector. -/
instance subsingleton_componentSumAmbient_nil : Subsingleton (componentSumAmbient []) :=
  inferInstanceAs (Subsingleton (Fin 0 → ℚ))

/-- The orthogonal sum of the empty component list: the zero lattice on the empty coordinate
space. -/
@[expose] noncomputable def emptyComponentSum : IntegralLattice (Fin 0 → ℚ) :=
  IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin 0)) 0 Matrix.isSymm_zero

/-- The orthogonal sum of an ordered component list: the iterated orthogonal sum of the component
root lattices, with the zero lattice for the empty list. -/
@[expose] noncomputable def componentSumLattice :
    (l : List Component) → IntegralLattice (componentSumAmbient l)
  | [] => emptyComponentSum
  | c :: cs => c.rootLattice.orthogonalSum (componentSumLattice cs)

/-- The orthogonal sum of a component list is even. -/
theorem isEven_componentSumLattice : (l : List Component) → (componentSumLattice l).IsEven
  | [] =>
    (IntegralLattice.isEven_ofGramMatrix_iff (Pi.basisFun ℚ (Fin 0)) 0 Matrix.isSymm_zero).mpr
      fun i => i.elim0
  | c :: cs =>
    (IntegralLattice.isEven_orthogonalSum_iff c.rootLattice (componentSumLattice cs)).mpr
      ⟨c.isEven_rootLattice, isEven_componentSumLattice cs⟩

/-- The orthogonal sum of a component list is nondegenerate. -/
instance isNondegenerate_componentSumLattice : (l : List Component) →
    (componentSumLattice l).IsNondegenerate
  | [] => ⟨⟨fun x _ => Subsingleton.elim x 0, fun x _ => Subsingleton.elim x 0⟩⟩
  | c :: cs =>
    letI : (componentSumLattice cs).IsNondegenerate := isNondegenerate_componentSumLattice cs
    inferInstanceAs ((c.rootLattice.orthogonalSum (componentSumLattice cs)).IsNondegenerate)

/-- The dependent coordinate product of the component glue alphabets along an ordered component
list: the finite quadratic module of glue words, with one label per component. -/
@[expose] noncomputable def componentAlphabet : List Component → FiniteQuadraticModule
  | [] => FiniteQuadraticModule.cyclic 1 0 (smul_zero _) (smul_zero _)
  | c :: cs => c.glueAlphabet.prod (componentAlphabet cs)

/-- The glue alphabet of the empty component list is the trivial finite quadratic module. -/
theorem componentAlphabet_nil :
    componentAlphabet [] = FiniteQuadraticModule.cyclic 1 0 (smul_zero _) (smul_zero _) :=
  (rfl)

/-- The trivial finite quadratic module is a subsingleton, so the empty glue word is unique. -/
instance subsingleton_componentAlphabet_nil : Subsingleton (componentAlphabet []) :=
  inferInstanceAs (Subsingleton (ZMod 1))

/-- The glue alphabet of a component list starting with `c` is the product of the alphabet of `c`
and the glue alphabet of the rest of the list. -/
theorem componentAlphabet_cons (c : Component) (cs : List Component) :
    componentAlphabet (c :: cs) = c.glueAlphabet.prod (componentAlphabet cs) :=
  (rfl)

/-- The discriminant group of the empty component sum is trivial. -/
instance subsingleton_discriminantGroup_empty :
    Subsingleton (componentSumLattice []).DiscriminantGroup :=
  inferInstanceAs (Subsingleton ((componentSumLattice []).dualCarrier ⧸
    (componentSumLattice []).carrierInDual))

/-- The discriminant quadratic module of the empty component sum is trivial. -/
instance subsingleton_discriminantQuadraticModule_empty :
    Subsingleton ((componentSumLattice []).discriminantQuadraticModule
      (isEven_componentSumLattice [])).carrier :=
  inferInstanceAs (Subsingleton (componentSumLattice []).DiscriminantGroup)

/-- **The discriminant form of an ordered component list in glue coordinates.**  The discriminant
quadratic module of the orthogonal sum of the component root lattices is isometric to the
dependent product of the component glue alphabets. -/
noncomputable def componentDiscriminantIsometry :
    (l : List Component) → FiniteQuadraticModule.Isometry (componentAlphabet l)
      ((componentSumLattice l).discriminantQuadraticModule (isEven_componentSumLattice l))
  | [] =>
    haveI : Subsingleton (componentAlphabet []) := subsingleton_componentAlphabet_nil
    haveI : Subsingleton ((componentSumLattice []).discriminantQuadraticModule
        (isEven_componentSumLattice [])) := subsingleton_discriminantGroup_empty
    FiniteQuadraticModule.Isometry.ofSubsingleton
  | c :: cs =>
    (QuadraticMap.IsometryEquiv.prod c.glueAlphabetIsometry
        (componentDiscriminantIsometry cs)).trans
      (IntegralLattice.discriminantQuadraticIsometryOrthogonalSum c.rootLattice
        (componentSumLattice cs) c.isEven_rootLattice
        (isEven_componentSumLattice cs)).symm

/-- The component-list isometry on a glue word: the component isometry applies to the leading
label, the component-list isometry to the remaining word, and the pair of discriminant classes is
transported to the orthogonal sum. -/
@[simp]
theorem componentDiscriminantIsometry_cons (c : Component) (cs : List Component)
    (x₁ : c.glueAlphabet) (x₂ : componentAlphabet cs) :
    componentDiscriminantIsometry (c :: cs) (x₁, x₂) =
      (IntegralLattice.discriminantQuadraticIsometryOrthogonalSum c.rootLattice
        (componentSumLattice cs) c.isEven_rootLattice (isEven_componentSumLattice cs)).symm
        (c.glueAlphabetIsometry x₁, componentDiscriminantIsometry cs x₂) :=
  (rfl)

end TauCeti.DynkinType

/-! ## Naturality of the component-list discriminant isometry

The list-level naturality statements below are pointwise, so their induction step needs the
orthogonal-sum discriminant isometry to be natural in its two arguments.  That naturality is
general integral-lattice infrastructure and is proved with the orthogonal-sum operations, in
`TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations`.
-/

namespace TauCeti.DynkinType

/-- The alphabet-level isometry induced by an isometry of a single component's root lattice. -/
noncomputable def componentGlueAlphabetIsometry {c d : Component}
    (f : IntegralLattice.Isometry c.rootLattice d.rootLattice) :
    FiniteQuadraticModule.Isometry c.glueAlphabet d.glueAlphabet :=
  c.glueAlphabetIsometry.trans
    ((f.discriminantQuadraticIsometry c.isEven_rootLattice).trans d.glueAlphabetIsometry.symm)

/-- An isometry of component root lattices is compatible with the component glue isometries: the
component glue isometry of the target component carries the transported label to the transport of
the source label. -/
theorem glueAlphabetIsometry_componentGlueAlphabetIsometry {c d : Component}
    (f : IntegralLattice.Isometry c.rootLattice d.rootLattice) (x : c.glueAlphabet) :
    d.glueAlphabetIsometry (componentGlueAlphabetIsometry f x) =
      f.discriminantQuadraticIsometry c.isEven_rootLattice (c.glueAlphabetIsometry x) := by
  rw [componentGlueAlphabetIsometry, FiniteQuadraticModule.Isometry.trans_apply,
    FiniteQuadraticModule.Isometry.trans_apply]
  exact QuadraticMap.IsometryEquiv.apply_symm_apply _ _

/-- A componentwise isometry of two ordered component lists: an isometry of the root lattice of each
component of the first list onto the root lattice of the corresponding component of the second.

This is data rather than a `List.Perm` of isometries, because `List.Perm` is a proposition, and the
induced isometries of the glue alphabets and of the component sums are data. -/
inductive ComponentIsometry : List Component → List Component → Type
  | /-- The empty lists are componentwise isometric. -/
    nil : ComponentIsometry [] []
  | /-- A component isometry of the two heads and a componentwise isometry of the two tails. -/
    cons {c d : Component} {cs ds : List Component}
      (f : IntegralLattice.Isometry c.rootLattice d.rootLattice)
      (rest : ComponentIsometry cs ds) : ComponentIsometry (c :: cs) (d :: ds)

/-- The isometry of component sums induced by a componentwise isometry of the component lists. -/
noncomputable def componentSumIsometry :
    {l₁ l₂ : List Component} → ComponentIsometry l₁ l₂ →
      IntegralLattice.Isometry (componentSumLattice l₁) (componentSumLattice l₂)
  | _, _, .nil => IntegralLattice.Isometry.refl _
  | _, _, .cons f rest => f.orthogonalSum (componentSumIsometry rest)

/-- The sum isometry of the empty componentwise isometry is the identity on the empty component
sum. -/
@[simp]
theorem componentSumIsometry_nil (x : componentSumAmbient []) :
    componentSumIsometry ComponentIsometry.nil x = x :=
  IntegralLattice.Isometry.refl_apply _ x

/-- The sum isometry of an adjoined component isometry acts componentwise on the leading component
and on the remaining component sum. -/
@[simp]
theorem componentSumIsometry_cons {c d : Component} {cs ds : List Component}
    (f : IntegralLattice.Isometry c.rootLattice d.rootLattice) (rest : ComponentIsometry cs ds)
    (x₁ : Fin c.rank → ℚ) (x₂ : componentSumAmbient cs) :
    componentSumIsometry (.cons f rest) (x₁, x₂) = (f x₁, componentSumIsometry rest x₂) :=
  IntegralLattice.Isometry.orthogonalSum_apply f (componentSumIsometry rest) (x₁, x₂)

/-- The isometry of glue alphabets induced by a componentwise isometry of the component lists. -/
noncomputable def componentAlphabetIsometry :
    {l₁ l₂ : List Component} → ComponentIsometry l₁ l₂ →
      FiniteQuadraticModule.Isometry (componentAlphabet l₁) (componentAlphabet l₂)
  | _, _, .nil =>
    haveI : Subsingleton (componentAlphabet []) := subsingleton_componentAlphabet_nil
    FiniteQuadraticModule.Isometry.ofSubsingleton
  | _, _, .cons f rest =>
    QuadraticMap.IsometryEquiv.prod (componentGlueAlphabetIsometry f)
      (componentAlphabetIsometry rest)

/-- The alphabet isometry of a componentwise isometry acts componentwise on glue words. -/
@[simp]
theorem componentAlphabetIsometry_cons {c d : Component} {cs ds : List Component}
    (f : IntegralLattice.Isometry c.rootLattice d.rootLattice) (rest : ComponentIsometry cs ds)
    (x₁ : c.glueAlphabet) (x₂ : componentAlphabet cs) :
    componentAlphabetIsometry (.cons f rest) (x₁, x₂) =
      (componentGlueAlphabetIsometry f x₁, componentAlphabetIsometry rest x₂) :=
  FiniteQuadraticModule.Isometry.prod_apply (componentGlueAlphabetIsometry f)
    (componentAlphabetIsometry rest) x₁ x₂

/-- **Naturality of the component-list discriminant isometry passes to an adjoined component.**  If
the component-list discriminant isometry is natural for the tails `cs` and `ds`, then it is natural
for the lists obtained by adjoining components `c` and `d` that are related by a root-lattice
isometry: a glue word `(x₁, x₂)` of `c :: cs` is transported by the component glue isometry on the
leading label and the tail isometry on the remaining word.  This is the induction step of
`componentDiscriminantIsometry_natural`. -/
private theorem componentDiscriminantIsometry_natural_cons {c d : Component}
    {cs ds : List Component}
    (f : IntegralLattice.Isometry c.rootLattice d.rootLattice) (rest : ComponentIsometry cs ds)
    (ih : ∀ w : componentAlphabet cs,
      (componentSumIsometry rest).discriminantQuadraticIsometry (isEven_componentSumLattice cs)
          (componentDiscriminantIsometry cs w) =
        componentDiscriminantIsometry ds (componentAlphabetIsometry rest w))
    (x₁ : c.glueAlphabet) (x₂ : componentAlphabet cs) :
    (f.orthogonalSum (componentSumIsometry rest)).discriminantQuadraticIsometry
        ((IntegralLattice.isEven_orthogonalSum_iff c.rootLattice (componentSumLattice cs)).mpr
          ⟨c.isEven_rootLattice, isEven_componentSumLattice cs⟩)
        ((IntegralLattice.discriminantQuadraticIsometryOrthogonalSum c.rootLattice
            (componentSumLattice cs) c.isEven_rootLattice
            (isEven_componentSumLattice cs)).symm
          (c.glueAlphabetIsometry x₁, componentDiscriminantIsometry cs x₂)) =
      (IntegralLattice.discriminantQuadraticIsometryOrthogonalSum d.rootLattice
          (componentSumLattice ds) d.isEven_rootLattice (isEven_componentSumLattice ds)).symm
        (d.glueAlphabetIsometry ((componentGlueAlphabetIsometry f) x₁),
          componentDiscriminantIsometry ds (componentAlphabetIsometry rest x₂)) := by
  have key := IntegralLattice.discriminantQuadraticIsometryOrthogonalSum_symm_apply
    (L := c.rootLattice) (M := componentSumLattice cs) (L' := d.rootLattice)
    (M' := componentSumLattice ds) f (componentSumIsometry rest) c.isEven_rootLattice
    (isEven_componentSumLattice cs) d.isEven_rootLattice (isEven_componentSumLattice ds)
    ((IntegralLattice.isEven_orthogonalSum_iff c.rootLattice (componentSumLattice cs)).mpr
      ⟨c.isEven_rootLattice, isEven_componentSumLattice cs⟩)
    (c.glueAlphabetIsometry x₁) (componentDiscriminantIsometry cs x₂)
  rw [key, ← glueAlphabetIsometry_componentGlueAlphabetIsometry, ih x₂]

/-- **Naturality of the component-list discriminant isometry under componentwise isometries.**  A
componentwise isometry of the component lists transports discriminant classes of the component sums
compatibly with the transport of the glue words: applying the component-list isometry and then the
induced sum isometry agrees with transporting the word and then applying the component-list
isometry. -/
theorem componentDiscriminantIsometry_natural :
    {l₁ l₂ : List Component} → (F : ComponentIsometry l₁ l₂) → ∀ w : componentAlphabet l₁,
      (componentSumIsometry F).discriminantQuadraticIsometry (isEven_componentSumLattice l₁)
          (componentDiscriminantIsometry l₁ w) =
        componentDiscriminantIsometry l₂ (componentAlphabetIsometry F w)
  | _, _, .nil, _ =>
    haveI : Subsingleton (componentSumLattice []).DiscriminantGroup :=
      subsingleton_discriminantGroup_empty
    Subsingleton.elim _ _
  | _, _, .cons f rest, (x₁, x₂) =>
    componentDiscriminantIsometry_natural_cons f rest
      (fun w => componentDiscriminantIsometry_natural rest w) x₁ x₂

end TauCeti.DynkinType
