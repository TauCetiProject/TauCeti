/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import TauCeti.GroupTheory.Coxeter.Geometric.Integral
public import TauCeti.GroupTheory.Presentation.Coxeter
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# The T246 reflection group modulo two

The **T246 diagram** has ten nodes `0, …, 9`: a chain `1 - 2 - ⋯ - 9` together with an edge
`0 - 4`. Its Coxeter group `W` (`TauCeti.reyeDiagram`) is the reflection group of the Reye lattice
`R` of a general nodal Enriques surface: `R` has a basis of ten roots `β₀, …, β₉` of square `-2`
whose intersection numbers `βᵢ · βⱼ` are `1` on the edges of the diagram and `0` off them, and
`W` acts on `R` by the reflections `x ↦ x + (x · βᵢ) βᵢ`. In these coordinates the action is
the integral realization of the Coxeter system `CoxeterSystem.reflectionRepresentation`, whose
`i`-th generator is `x ↦ x - (∑ⱼ xⱼ Aᵢⱼ) eᵢ` for the integral Gram matrix
`A = reyeDiagram.integralGramMatrix`, with `2` on the diagonal and `-1` on the edges.

This file studies the reduction of that action modulo `2`, on `H = R / 2R = F₂¹⁰`
(`TauCeti.ReyeReduction`). Half the norm of the lattice reduces to the quadratic form

`q(x) = ∑ᵢ xᵢ + ∑_{edges {i, j}} xᵢ xⱼ`

over `F₂` (`TauCeti.reyeQuadratic`), each edge counted once. Its polar form
`b(x, y) = ∑_{edges {i, j}} (xᵢ yⱼ + xⱼ yᵢ)` is alternating, and:

* the radical of `b` is the plane spanned by `u = e₀ + e₅ + e₇ + e₉` and
  `z = e₁ + e₃ + e₅ + e₇ + e₉` (`TauCeti.ker_polarBilin_reyeQuadratic`), and `q(a u + b z) = b`
  (`TauCeti.reyeQuadratic_smul_add_smul`), so `q` does not descend to the eight-dimensional
  symplectic quotient by the radical;
* each simple generator acts on `H` by the orthogonal reflection `x ↦ x + b(x, eᵢ) eᵢ` of `q` in
  the vector `eᵢ` of norm one, which in characteristic two is a transvection. These satisfy the
  Coxeter relations of T246, which gives the action `TauCeti.reyeReductionAction` of `W` on `H`
  by isometries of `q`; it is the reduction modulo `2` of the integral action on `R`
  (`TauCeti.reyeReductionAction_apply_intCast`);
* every element of `W` fixes the radical of `b` pointwise
  (`TauCeti.range_reyeReductionAction_le_fixingSubgroup`).

The Coxeter relations are not checked by hand: they are transported from the integral realization
of the Coxeter system through `CoxeterMatrix.isLiftable_preReflection_map`.

## Main definitions

* `TauCeti.reyeDiagram`: the Coxeter matrix of the T246 diagram.
* `TauCeti.reyeQuadratic`: the quadratic form `q` on `TauCeti.ReyeReduction = Fin 10 → ZMod 2`.
* `TauCeti.reyeRadicalU`, `TauCeti.reyeRadicalZ`: the vectors `u` and `z` spanning the polar
  radical.
* `TauCeti.reyeReductionAction`: the action of the T246 Coxeter group on `F₂¹⁰` by isometries of
  `q`.

## Main results

* `TauCeti.ker_polarBilin_reyeQuadratic`: the radical of the polar form is `⟨u, z⟩`, and
  `TauCeti.finrank_ker_polarBilin_reyeQuadratic`: it is two-dimensional.
* `TauCeti.reyeQuadratic_smul_add_smul`: `q(a u + b z) = b`.
* `TauCeti.reyeReductionAction_simple_apply`: the simple generator `sᵢ` acts by
  `x ↦ x + b(x, eᵢ) eᵢ`.
* `TauCeti.reyeReductionAction_apply_intCast`: the action is the reduction modulo `2` of the
  integral reflection representation.
* `TauCeti.range_reyeReductionAction_le_fixingSubgroup`: the image consists of isometries of `q`
  fixing the polar radical pointwise.

## References

* F. Cossec, I. Dolgachev, *On automorphisms of nodal Enriques surfaces*, Bull. Amer. Math. Soc.
  12 (1985), 247–249, §2 and Proposition 1.
* C. Peters, H. Sterk, *On K3 double planes covering Enriques surfaces*, Math. Ann. 376 (2020),
  1599–1628, Appendix A.2, Lemma A.5.
-/

public section

open QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup reflection reflectionOrthogonal reflection_apply
  coe_reflectionOrthogonal)

namespace TauCeti

/-! ### The T246 diagram -/

/-- The nine edges of the T246 diagram, each listed once: the chain `1 - 2 - ⋯ - 9` and the edge
`0 - 4`. -/
@[expose]
def reyeEdges : List (Fin 10 × Fin 10) :=
  [(0, 4), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)]

/-- The Coxeter matrix of the T246 diagram: entry `1` on the diagonal, `3` on the edges
`reyeEdges` and `2` elsewhere. -/
@[expose]
def reyeDiagram : CoxeterMatrix (Fin 10) :=
  coxeterMatrixOfEdges reyeEdges

/-- Entrywise formula for `reyeDiagram`. -/
theorem reyeDiagram_apply (i j : Fin 10) :
    reyeDiagram i j =
      if i = j then 1 else if (i, j) ∈ reyeEdges ∨ (j, i) ∈ reyeEdges then 3 else 2 :=
  coxeterMatrixOfEdges_apply reyeEdges i j

/-- The T246 diagram is simply laced: every entry of its Coxeter matrix is at most `3`. -/
theorem reyeDiagram_le_three (i j : Fin 10) : reyeDiagram i j ≤ 3 := by
  rw [reyeDiagram_apply]
  split_ifs <;> decide

/-- The integral Gram matrix of the T246 diagram is twice its canonical form: its entries are `2`
on the diagonal, `-1` on the edges and `0` elsewhere, and `-2 cos (π / 3) = -1`. -/
theorem algebraMap_integralGramMatrix_reyeDiagram (i j : Fin 10) :
    algebraMap ℤ ℝ (reyeDiagram.integralGramMatrix i j) =
      2 * reyeDiagram.geometricForm (Finsupp.single i 1) (Finsupp.single j 1) :=
  reyeDiagram.algebraMap_integralGramMatrix_eq_two_mul_geometricForm_of_le_three
    (reyeDiagram_le_three i j)

/-! ### The quadratic form on `F₂¹⁰` -/

/-- The reduction `R / 2R` of the Reye lattice, in the coordinates of its basis of simple roots. -/
abbrev ReyeReduction := Fin 10 → ZMod 2

/-- The quadratic form `q(x) = ∑ᵢ xᵢ + ∑_{edges {i, j}} xᵢ xⱼ` on `F₂¹⁰`, the reduction modulo `2`
of half the norm of the Reye lattice. Since `xᵢ² = xᵢ` over `F₂`, it is written as
`∑ᵢ xᵢ² + ∑_{edges} xᵢ xⱼ` (see `TauCeti.reyeQuadratic_apply`). -/
noncomputable def reyeQuadratic : QuadraticForm (ZMod 2) ReyeReduction :=
  ∑ i, QuadraticMap.proj i i + (reyeEdges.map fun e ↦ QuadraticMap.proj e.1 e.2).sum

/-- The defining formula `q(x) = ∑ᵢ xᵢ + ∑_{edges {i, j}} xᵢ xⱼ`. -/
theorem reyeQuadratic_apply (x : ReyeReduction) :
    reyeQuadratic x = ∑ i, x i + (reyeEdges.map fun e ↦ x e.1 * x e.2).sum := by
  have hsq (a : ZMod 2) : a * a = a := by fin_cases a <;> rfl
  simp [reyeQuadratic, reyeEdges, QuadraticMap.proj_apply, hsq]

/-- The polar form of `reyeQuadratic` is `b(x, y) = ∑_{edges {i, j}} (xᵢ yⱼ + yᵢ xⱼ)`. -/
theorem polar_reyeQuadratic (x y : ReyeReduction) :
    polar reyeQuadratic x y = (reyeEdges.map fun e ↦ x e.1 * y e.2 + y e.1 * x e.2).sum := by
  simp only [polar, reyeQuadratic_apply, reyeEdges]
  simp [Fin.sum_univ_succ]
  ring

/-- Every simple root has norm one: `q(eᵢ) = 1`. -/
@[simp]
theorem reyeQuadratic_single (i : Fin 10) : reyeQuadratic (Pi.single i 1) = 1 := by
  rw [reyeQuadratic_apply]
  revert i
  decide

/-- The polar form of `reyeQuadratic` on the simple roots is the reduction modulo `2` of the
integral Gram matrix of the T246 diagram. -/
theorem polar_reyeQuadratic_single_single (i j : Fin 10) :
    polar reyeQuadratic (Pi.single i 1) (Pi.single j 1) =
      Int.castRingHom (ZMod 2) (reyeDiagram.integralGramMatrix i j) := by
  rw [polar_reyeQuadratic, CoxeterMatrix.integralGramMatrix_apply]
  revert i j
  decide

/-! ### The radical of the polar form -/

/-- The vector `u = e₀ + e₅ + e₇ + e₉` of the polar radical, with `q(u) = 0`. -/
@[expose]
def reyeRadicalU : ReyeReduction := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]

/-- The vector `z = e₁ + e₃ + e₅ + e₇ + e₉` of the polar radical, with `q(z) = 1`. -/
@[expose]
def reyeRadicalZ : ReyeReduction := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

private theorem polarBilin_reyeRadicalU : polarBilin reyeQuadratic reyeRadicalU = 0 := by
  ext i
  simp only [LinearMap.comp_apply, LinearMap.single_apply, polarBilin_apply_apply,
    polar_reyeQuadratic, LinearMap.zero_apply]
  revert i
  decide

private theorem polarBilin_reyeRadicalZ : polarBilin reyeQuadratic reyeRadicalZ = 0 := by
  ext i
  simp only [LinearMap.comp_apply, LinearMap.single_apply, polarBilin_apply_apply,
    polar_reyeQuadratic, LinearMap.zero_apply]
  revert i
  decide

/-- A vector orthogonal to every simple root is the combination `(x₅ + x₁) u + x₁ z`. -/
private theorem smul_reyeRadicalU_add_smul_reyeRadicalZ_of_polarBilin_eq_zero
    {x : ReyeReduction} (hx : polarBilin reyeQuadratic x = 0) :
    (x 5 + x 1) • reyeRadicalU + x 1 • reyeRadicalZ = x := by
  have h i := LinearMap.congr_fun hx (Pi.single i 1)
  simp only [polarBilin_apply_apply, polar_reyeQuadratic, LinearMap.zero_apply, reyeEdges] at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have h5 := h 5; have h6 := h 6; have h7 := h 7; have h8 := h 8; have h9 := h 9
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  funext k
  fin_cases k <;> simp [reyeRadicalU, reyeRadicalZ] <;> grind

/-- **The radical of the polar form** of `reyeQuadratic` is the plane spanned by
`u = e₀ + e₅ + e₇ + e₉` and `z = e₁ + e₃ + e₅ + e₇ + e₉`. -/
theorem ker_polarBilin_reyeQuadratic :
    LinearMap.ker (polarBilin reyeQuadratic) =
      Submodule.span (ZMod 2) {reyeRadicalU, reyeRadicalZ} := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_pair]
  refine ⟨fun hx ↦ ⟨_, _, smul_reyeRadicalU_add_smul_reyeRadicalZ_of_polarBilin_eq_zero hx⟩, ?_⟩
  rintro ⟨a, b, rfl⟩
  simp [polarBilin_reyeRadicalU, polarBilin_reyeRadicalZ]

/-- The vectors `u` and `z` are linearly independent, so the polar radical is a plane. -/
theorem linearIndependent_reyeRadical :
    LinearIndependent (ZMod 2) ![reyeRadicalU, reyeRadicalZ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simpa [reyeRadicalU, reyeRadicalZ] using And.intro (congr_fun hst 0) (congr_fun hst 1)

/-- The radical of the polar form of `reyeQuadratic` is two-dimensional, so the polar form induces
a nondegenerate alternating form on an eight-dimensional quotient. -/
theorem finrank_ker_polarBilin_reyeQuadratic :
    Module.finrank (ZMod 2) (LinearMap.ker (polarBilin reyeQuadratic)) = 2 := by
  rw [ker_polarBilin_reyeQuadratic, ← Matrix.range_cons_cons_empty _ _ ![],
    finrank_span_eq_card linearIndependent_reyeRadical, Fintype.card_fin]

/-- **`q` is not constant on the cosets of the polar radical**: `q(a u + b z) = b`. -/
theorem reyeQuadratic_smul_add_smul (a b : ZMod 2) :
    reyeQuadratic (a • reyeRadicalU + b • reyeRadicalZ) = b := by
  rw [reyeQuadratic_apply]
  revert a b
  decide

/-! ### The action of the T246 Coxeter group -/

/-- The norm `q(eᵢ) = 1` of a simple root is invertible, so that the orthogonal reflection of
`reyeQuadratic` in `eᵢ` is defined. -/
instance (i : Fin 10) : Invertible (reyeQuadratic (Pi.single i 1)) where
  invOf := 1
  invOf_mul_self := by rw [reyeQuadratic_single, mul_one]
  mul_invOf_self := by rw [reyeQuadratic_single, mul_one]

/-- The orthogonal reflection of `reyeQuadratic` in the simple root `eᵢ` is the transvection
`x ↦ x + b(x, eᵢ) eᵢ`. -/
@[simp]
theorem reflection_reyeQuadratic_single_apply (i : Fin 10) (x : ReyeReduction) :
    reflection reyeQuadratic (Pi.single i 1) x =
      x + polar reyeQuadratic x (Pi.single i 1) • Pi.single i 1 := by
  rw [reflection_apply, polar_comm, sub_eq_add_neg, ← neg_smul, ZMod.neg_eq_self_mod_two]
  congr 2
  exact one_mul _

/-- In the coordinates `Fin 10 →₀ ZMod 2`, the reflection of `reyeQuadratic` in `eᵢ` is the
`i`-th reflection of the integral Gram matrix of T246 reduced modulo `2`. -/
private theorem reflection_reyeQuadratic_single_coe (i : Fin 10) (y : Fin 10 →₀ ZMod 2) :
    reflection reyeQuadratic (Pi.single i 1) y =
      Module.preReflection (Finsupp.single i 1)
        (Finsupp.linearCombination (ZMod 2)
          (reyeDiagram.integralGramMatrix.map (Int.castRingHom (ZMod 2)) i)) y := by
  have h := Finsupp.lhom_ext' (φ := (reflection reyeQuadratic (Pi.single i 1)).toLinearMap ∘ₗ
      Finsupp.lcoeFun)
    (ψ := Finsupp.lcoeFun ∘ₗ Module.preReflection (Finsupp.single i 1)
      (Finsupp.linearCombination (ZMod 2)
        (reyeDiagram.integralGramMatrix.map (Int.castRingHom (ZMod 2)) i))) fun k ↦
    LinearMap.ext_ring <| by
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lcoeFun_apply,
        LinearEquiv.coe_coe, reflection_reyeQuadratic_single_apply, Module.preReflection_apply,
        Finsupp.single_eq_pi_single, Finsupp.linearCombination_single, Matrix.map_apply,
        polar_comm _ (Pi.single k 1), polar_reyeQuadratic_single_single, one_smul,
        sub_eq_add_neg, ← neg_smul, ZMod.neg_eq_self_mod_two, Finsupp.coe_add, Finsupp.coe_smul]
  exact LinearMap.congr_fun h y

/-- The orthogonal reflections of `reyeQuadratic` in the simple roots satisfy the Coxeter relations
of the T246 diagram. They are inherited from the integral realization of the Coxeter system through
the injective conjugation by `Finsupp.linearEquivFunOnFinite`. -/
theorem isLiftable_reflectionOrthogonal_reyeQuadratic :
    reyeDiagram.IsLiftable fun i ↦ reflectionOrthogonal reyeQuadratic (Pi.single i 1) := by
  have hP := CoxeterMatrix.isLiftable_preReflection_map
    (CoxeterMatrix.isLiftable_preReflection (algebraMap ℤ ℝ).injective_int
      algebraMap_integralGramMatrix_reyeDiagram)
    (Int.castRingHom (ZMod 2))
  let e := Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin 10)
  let ψ : orthogonalGroup reyeQuadratic →* Module.End (ZMod 2) (Fin 10 →₀ ZMod 2) :=
    (e.symm.conjRingEquiv : Module.End (ZMod 2) ReyeReduction →* _).comp
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (orthogonalGroup _).subtype)
  have hψ : Function.Injective ψ := by
    intro g h hgh
    refine Subtype.ext (LinearEquiv.ext fun y ↦ ?_)
    simpa [ψ] using LinearMap.congr_fun hgh (e.symm y)
  have hψi (i : Fin 10) : ψ (reflectionOrthogonal reyeQuadratic (Pi.single i 1)) =
      Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination (ZMod 2)
        (reyeDiagram.integralGramMatrix.map (Int.castRingHom (ZMod 2)) i)) := by
    refine LinearMap.ext fun y ↦ DFunLike.coe_injective ?_
    simp only [ψ, e, MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.coe_ofClass,
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply,
      LinearEquiv.conjRingEquiv_apply_apply, LinearEquiv.coe_coe,
      Finsupp.linearEquivFunOnFinite_symm_apply, LinearEquiv.symm_symm, coe_reflectionOrthogonal]
    exact reflection_reyeQuadratic_single_coe i y
  intro i j
  apply hψ
  rw [map_pow, map_mul, map_one, hψi, hψi]
  exact hP i j

/-- **The T246 Coxeter group acting on `F₂¹⁰`** by isometries of `reyeQuadratic`: the simple
generator `sᵢ` acts by the orthogonal reflection of `reyeQuadratic` in `eᵢ`, which is the
transvection `x ↦ x + b(x, eᵢ) eᵢ` (`TauCeti.reyeReductionAction_simple_apply`). It is the action
of the reflection group of the Reye lattice `R` on `R / 2R`
(`TauCeti.reyeReductionAction_apply_intCast`). -/
noncomputable def reyeReductionAction : reyeDiagram.Group →* orthogonalGroup reyeQuadratic :=
  reyeDiagram.toCoxeterSystem.lift ⟨_, isLiftable_reflectionOrthogonal_reyeQuadratic⟩

/-- The simple generator `sᵢ` acts by the orthogonal reflection of `reyeQuadratic` in `eᵢ`. -/
@[simp]
theorem reyeReductionAction_simple (i : Fin 10) :
    reyeReductionAction (reyeDiagram.simple i) =
      reflectionOrthogonal reyeQuadratic (Pi.single i 1) := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact reyeDiagram.toCoxeterSystem.lift_apply_simple
    isLiftable_reflectionOrthogonal_reyeQuadratic i

/-- **The generator formula**: `sᵢ` acts on `F₂¹⁰` by `x ↦ x + b(x, eᵢ) eᵢ`. -/
theorem reyeReductionAction_simple_apply (i : Fin 10) (x : ReyeReduction) :
    (reyeReductionAction (reyeDiagram.simple i) : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x =
      x + polar reyeQuadratic x (Pi.single i 1) • Pi.single i 1 := by
  rw [reyeReductionAction_simple, coe_reflectionOrthogonal,
    reflection_reyeQuadratic_single_apply]

/-- In the coordinates `Fin 10 →₀ ZMod 2`, the action is the reflection representation of the
integral Gram matrix of T246 reduced modulo `2`. -/
private theorem reyeReductionAction_apply_coe (w : reyeDiagram.Group) (y : Fin 10 →₀ ZMod 2) :
    (reyeReductionAction w : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) y =
      reyeDiagram.toCoxeterSystem.mapReflectionRepresentation (algebraMap ℤ ℝ).injective_int
        algebraMap_integralGramMatrix_reyeDiagram
        (Int.castRingHom (ZMod 2)) w y := by
  induction w using reyeDiagram.toCoxeterSystem.simple_induction generalizing y with
  | simple i =>
    rw [CoxeterSystem.mapReflectionRepresentation_simple, CoxeterMatrix.toCoxeterSystem_simple,
      reyeReductionAction_simple, coe_reflectionOrthogonal, reflection_reyeQuadratic_single_coe]
  | one => simp
  | mul w₁ w₂ hw₁ hw₂ =>
    simp only [map_mul, Subgroup.coe_mul, mul_apply_eq_comp, mul_apply_eq_comp, hw₂, hw₁]

/-- **The action on `F₂¹⁰` is the reduction modulo `2` of the integral action** of the T246
Coxeter group on `ℤ¹⁰`, the reflection representation of its integral Gram matrix, which is the
action on the Reye lattice in the coordinates of its simple roots. -/
theorem reyeReductionAction_apply_intCast (w : reyeDiagram.Group) (x : Fin 10 →₀ ℤ) :
    (reyeReductionAction w : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) (fun k ↦ (x k : ZMod 2)) =
      fun k ↦ (reyeDiagram.toCoxeterSystem.reflectionRepresentation
        (algebraMap ℤ ℝ).injective_int
        algebraMap_integralGramMatrix_reyeDiagram w x k : ZMod 2) := by
  have h := reyeReductionAction_apply_coe w (x.mapRange (Int.castRingHom (ZMod 2)) (map_zero _))
  have hc (y : Fin 10 →₀ ℤ) :
      ⇑(y.mapRange (Int.castRingHom (ZMod 2)) (map_zero _)) = fun k ↦ (y k : ZMod 2) :=
    funext fun k ↦ by simp
  rwa [← CoxeterSystem.mapRange_ringHom_reflectionRepresentation, hc, hc] at h

/-- Every element of the T246 Coxeter group fixes the radical of the polar form pointwise. -/
theorem reyeReductionAction_apply_of_mem_ker (w : reyeDiagram.Group) {x : ReyeReduction}
    (hx : x ∈ LinearMap.ker (polarBilin reyeQuadratic)) :
    (reyeReductionAction w : ReyeReduction ≃ₗ[ZMod 2] ReyeReduction) x = x := by
  rw [LinearMap.mem_ker] at hx
  induction w using reyeDiagram.toCoxeterSystem.simple_induction with
  | simple i =>
    rw [CoxeterMatrix.toCoxeterSystem_simple, reyeReductionAction_simple_apply,
      ← polarBilin_apply_apply, hx]
    simp
  | one => simp
  | mul w₁ w₂ hw₁ hw₂ =>
    simp only [map_mul, Subgroup.coe_mul, mul_apply_eq_comp, hw₂, hw₁]

/-- **The image of the T246 Coxeter group in the orthogonal group of `q`** consists of isometries
fixing the radical `⟨u, z⟩` of the polar form pointwise. -/
theorem range_reyeReductionAction_le_fixingSubgroup :
    reyeReductionAction.range ≤ fixingSubgroup (orthogonalGroup reyeQuadratic)
      (LinearMap.ker (polarBilin reyeQuadratic) : Set ReyeReduction) := by
  rintro _ ⟨w, rfl⟩
  rw [mem_fixingSubgroup_iff]
  exact fun x hx ↦ reyeReductionAction_apply_of_mem_ker w hx

end TauCeti
