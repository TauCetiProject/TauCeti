/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Equivalence
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.D4Six.Lattice
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality

/-!
# Hexacode automorphisms act on the Niemeier lattice `D₄⁶`

The Niemeier lattice `D₄⁶ = TauCeti.d4SixLattice` is glued from six copies of the root lattice
`D₄` along a subgroup of glue words which, read in a field `F = F₄` of four elements and scaled
by `[ω, ω, 1, ω², ω², 1]`, is the hexacode (`TauCeti.mem_d4SixGlueSubgroup_iff`). This file shows
that every monomial automorphism of the hexacode induces an isometry of `D₄⁶` through that
identification.

The permutation part of a monomial transformation permutes the six `D₄` components. Its scalar
part is a nonzero element of `F₄` in each coordinate, and the nonzero scalars act on the `D₄`
glue alphabet through powers of the triality isometry of `D₄`
(`TauCeti.DynkinType.typeD4ScalarIsometry`). Thus:

* `TauCeti.d4SixMonomialIsometry u σ` applies the triality power realizing `u a` to the `D₄`
  component in position `a` and moves it to position `σ a`. On glue words, read in `F₄` through
  `TauCeti.typeD4GlueAlphabetQuaternaryIsometry`, it multiplies the label in position `a` by
  `u a` and moves it to position `σ a`. If that transformation preserves the glue subgroup, the
  isometry of the orthogonal sum of root lattices restricts to a self-isometry of `D₄⁶`.
* A monomial automorphism `monomialEquiv u σ` of `Hexacode.code ω` acts on hexacode
  coordinates. The scalings `c = [ω, ω, 1, ω², ω², 1]` of `TauCeti.d4SixHexacodeIsometry`
  conjugate it to the monomial transformation of label coordinates with scalars
  `c (σ a)⁻¹ * u a * c a` and the same permutation
  (`TauCeti.d4SixHexacodeIsometry_conj_monomialEquiv`). It therefore preserves the glue subgroup,
  and `TauCeti.d4SixHexacodeAutIsometry` is the induced self-isometry of `D₄⁶`.

The code automorphisms, the transformations of glue words and the lattice isometries are kept
distinct; the evaluation lemmas record how they are related.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §§3 and 7.1, Chapter 7, §§8–9, and Chapter 16, §1.
-/

public section

namespace TauCeti

open DynkinType IntegralLattice

variable {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

/-! ### Triality-scaled permutations of the components -/

/-- The triality-scaled permutation `u, σ` of the six `D₄` components acts on glue words, read in
`F₄`, by multiplying the label in position `a` by `u a` and moving it to position `σ a`.

The proof follows the pattern of `gluedLatticeSignedPermIsometry` in
https://github.com/TauCetiProject/TauCeti/pull/24752. -/
private theorem discriminantQuadraticIsometry_d4SixMonomial_glueWordIsometry (u : Fin 6 → Fˣ)
    (σ : Equiv.Perm (Fin 6)) (w : d4SixGlueModule) :
    ((Isometry.pi fun a ↦ typeD4ScalarIsometry (isSimplyLaced_D 4) hF hω (u a)).trans
        (Isometry.piCongrLeft (fun _ : Fin 6 ↦ (D 4).rootLattice (isSimplyLaced_D 4))
          σ)).discriminantQuadraticIsometry (isEven_pi_rootLattice _ _)
        (glueWordIsometry (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4)
          (fun _ ↦ valid_D.mpr le_rfl) w) =
      glueWordIsometry (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4)
        (fun _ ↦ valid_D.mpr le_rfl) fun j ↦ (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
          (u (σ.symm j) * typeD4GlueAlphabetQuaternaryIsometry hF hω (w (σ.symm j))) := by
  -- The scalars act first, componentwise, and the permutation then moves the components.
  have h1 := (Isometry.discriminantQuadraticIsometry_apply _ (isEven_pi_rootLattice _ _)
    _).symm.trans (discriminantQuadraticIsometry_pi_glueWordIsometry (fun _ : Fin 6 ↦ D 4)
      (fun _ ↦ isSimplyLaced_D 4) (fun _ ↦ valid_D.mpr le_rfl) (fun _ ↦ valid_D.mpr le_rfl)
      (fun a ↦ typeD4ScalarIsometry (isSimplyLaced_D 4) hF hω (u a))
      (fun a x ↦ (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        (u a * typeD4GlueAlphabetQuaternaryIsometry hF hω x))
      (fun a x ↦ ((Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
        (discriminantGroupEquiv_typeD4ScalarIsometry_glueAlphabetIsometry _ _ hF hω _ x)).symm) w)
  have h2 := (Isometry.discriminantQuadraticIsometry_apply _ (isEven_pi_rootLattice _ _)
    _).symm.trans (discriminantQuadraticIsometry_piCongrLeft_glueWordIsometry
      (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4) (fun _ ↦ valid_D.mpr le_rfl) σ
      (fun a ↦ (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        (u a * typeD4GlueAlphabetQuaternaryIsometry hF hω (w a))))
  refine (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans ?_
  rw [Isometry.discriminantGroupEquiv_trans]
  refine (LinearEquiv.trans_apply _).trans ?_
  rw [h1]
  refine h2.trans (congrArg _ (funext fun j ↦ ?_))
  obtain ⟨k, rfl⟩ := σ.surjective j
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

/-- **Triality-scaled permutations of the components preserving the glue subgroup are isometries
of `D₄⁶`.** For units `u : Fin 6 → Fˣ` and a permutation `σ`, apply to the `D₄` component in
position `a` the power `typeD4ScalarIsometry (u a)` of triality and move it to position `σ a`. On
glue words, read in `F₄` through `typeD4GlueAlphabetQuaternaryIsometry`, this multiplies the
label in position `a` by `u a` and moves it to position `σ a`. If that transformation maps the
glue subgroup of `D₄⁶` onto itself, the isometry restricts to a self-isometry of `D₄⁶`. -/
noncomputable def d4SixMonomialIsometry (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ w : d4SixGlueModule,
      (fun j ↦ (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
          (u (σ.symm j) * typeD4GlueAlphabetQuaternaryIsometry hF hω (w (σ.symm j))) :
        d4SixGlueModule) ∈ d4SixGlueSubgroup ↔ w ∈ d4SixGlueSubgroup) :
    Isometry d4SixLattice d4SixLattice :=
  (Isometry.ofEq d4SixLattice_def).trans <|
    (gluedLatticeIsometry _ _ _ _ _ _ _
      ((Isometry.pi fun a ↦ typeD4ScalarIsometry (isSimplyLaced_D 4) hF hω (u a)).trans
        (Isometry.piCongrLeft (fun _ : Fin 6 ↦ (D 4).rootLattice (isSimplyLaced_D 4)) σ))
      _ (discriminantQuadraticIsometry_d4SixMonomial_glueWordIsometry hF hω u σ) hσ).trans
      (Isometry.ofEq d4SixLattice_def.symm)

/-- The isometry `d4SixMonomialIsometry u σ` applies `typeD4ScalarIsometry (u a)` to the
component in position `a` and moves it to position `σ a`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the left-hand side by `rank_D`.
theorem d4SixMonomialIsometry_apply (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ w : d4SixGlueModule,
      (fun j ↦ (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
          (u (σ.symm j) * typeD4GlueAlphabetQuaternaryIsometry hF hω (w (σ.symm j))) :
        d4SixGlueModule) ∈ d4SixGlueSubgroup ↔ w ∈ d4SixGlueSubgroup)
    (x : Fin 6 → Fin (D 4).rank → ℚ) (j : Fin 6) :
    d4SixMonomialIsometry hF hω u σ hσ x j =
      typeD4ScalarIsometry (isSimplyLaced_D 4) hF hω (u (σ.symm j)) (x (σ.symm j)) := by
  obtain ⟨k, rfl⟩ := σ.surjective j
  simp only [d4SixMonomialIsometry, Isometry.trans_apply, Isometry.ofEq_apply,
    gluedLatticeIsometry_apply, Isometry.piCongrLeft_apply_apply, Isometry.pi_apply,
    Equiv.symm_apply_apply]

/-! ### Monomial automorphisms of the hexacode -/

/-- **A monomial automorphism of the hexacode, read in the label coordinates of `D₄⁶`.** If
`monomialEquiv u σ` multiplies hexacode coordinate `a` by `u a` and moves it to `σ a`, then the
corresponding transformation of label coordinates multiplies the label in position `a` by
`c (σ a)⁻¹ * u a * c a` and moves it to `σ a`, for the scalings `c = d4SixHexacodeScaling`: in
hexacode coordinates, the transformed glue word is `monomialEquiv u σ` of the original one. -/
theorem d4SixHexacodeIsometry_conj_monomialEquiv (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (w : d4SixGlueModule) :
    d4SixHexacodeIsometry hF hω (fun j ↦ (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        (((d4SixHexacodeScaling hω (σ (σ.symm j)))⁻¹ * u (σ.symm j) *
            d4SixHexacodeScaling hω (σ.symm j) : Fˣ) *
          typeD4GlueAlphabetQuaternaryIsometry hF hω (w (σ.symm j)))) =
      monomialEquiv u σ (d4SixHexacodeIsometry hF hω w) := by
  funext j
  have hc := (d4SixHexacodeScaling hω j).mul_inv
  -- `simp` does not rewrite these evaluations: the carrier of the codomain of the isometries is
  -- not syntactically a function type.
  rw [d4SixHexacodeIsometry_apply, d4SixQuaternaryIsometry_apply, monomialEquiv_apply,
    d4SixHexacodeIsometry_apply, d4SixQuaternaryIsometry_apply]
  simp only [QuadraticMap.IsometryEquiv.apply_symm_apply, Equiv.apply_symm_apply, Units.val_mul,
    coe_d4SixHexacodeScaling] at hc ⊢
  linear_combination (u (σ.symm j) * ![ω, ω, 1, ω ^ 2, ω ^ 2, 1] (σ.symm j) *
    typeD4GlueAlphabetQuaternaryIsometry hF hω (w (σ.symm j)) : F) * hc

/-- **A monomial automorphism of the hexacode preserves the glue subgroup of `D₄⁶`.** If
`monomialEquiv u σ` maps `Hexacode.code ω` onto itself, then multiplying the label in position `a`
by `c (σ a)⁻¹ * u a * c a`, for the scalings `c = d4SixHexacodeScaling`, and moving it to position
`σ a` maps the glue subgroup onto itself. -/
theorem mem_d4SixGlueSubgroup_hexacodeAut_iff (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (he : monomialEquiv u σ ∈ monomialAut (Hexacode.code ω)) (w : d4SixGlueModule) :
    (fun j ↦ (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        (((d4SixHexacodeScaling hω (σ (σ.symm j)))⁻¹ * u (σ.symm j) *
            d4SixHexacodeScaling hω (σ.symm j) : Fˣ) *
          typeD4GlueAlphabetQuaternaryIsometry hF hω (w (σ.symm j))) : d4SixGlueModule) ∈
        d4SixGlueSubgroup ↔ w ∈ d4SixGlueSubgroup := by
  rw [mem_d4SixGlueSubgroup_iff hF hω, mem_d4SixGlueSubgroup_iff hF hω,
    d4SixHexacodeIsometry_conj_monomialEquiv]
  conv_lhs => rw [← (mem_monomialAut.mp he).2, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

/-- **A monomial automorphism of the hexacode induces an isometry of `D₄⁶`.** Let
`monomialEquiv u σ`, multiplying hexacode coordinate `a` by `u a` and moving it to `σ a`, map
`Hexacode.code ω` onto itself. Then applying to the `D₄` component in position `a` the power of
triality realizing `c (σ a)⁻¹ * u a * c a`, for the hexacode scalings
`c = d4SixHexacodeScaling`, and moving it to position `σ a` is a self-isometry of the Niemeier
lattice `D₄⁶`. On glue words, read in hexacode coordinates, it acts as `monomialEquiv u σ`
(`d4SixHexacodeIsometry_conj_monomialEquiv`). -/
noncomputable def d4SixHexacodeAutIsometry (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (he : monomialEquiv u σ ∈ monomialAut (Hexacode.code ω)) :
    Isometry d4SixLattice d4SixLattice :=
  d4SixMonomialIsometry hF hω
    (fun a ↦ (d4SixHexacodeScaling hω (σ a))⁻¹ * u a * d4SixHexacodeScaling hω a) σ
    (mem_d4SixGlueSubgroup_hexacodeAut_iff hF hω u σ he)

/-- The isometry of `D₄⁶` induced by a hexacode automorphism `monomialEquiv u σ` moves the
component in position `σ.symm j` to position `j`, after applying the power of triality realizing
`c j⁻¹ * u (σ.symm j) * c (σ.symm j)`, for the hexacode scalings `c = d4SixHexacodeScaling`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the left-hand side by `rank_D`.
theorem d4SixHexacodeAutIsometry_apply (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (he : monomialEquiv u σ ∈ monomialAut (Hexacode.code ω))
    (x : Fin 6 → Fin (D 4).rank → ℚ) (j : Fin 6) :
    d4SixHexacodeAutIsometry hF hω u σ he x j =
      typeD4ScalarIsometry (isSimplyLaced_D 4) hF hω
        ((d4SixHexacodeScaling hω j)⁻¹ * u (σ.symm j) * d4SixHexacodeScaling hω (σ.symm j))
        (x (σ.symm j)) := by
  rw [d4SixHexacodeAutIsometry, d4SixMonomialIsometry_apply, Equiv.apply_symm_apply]

end TauCeti
