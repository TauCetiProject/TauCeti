/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.CyclesQuotient
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.KleinBottle
public import TauCeti.Geometry.Manifold.Morse.Bott.Complex
import Mathlib.Data.ZMod.QuotientRing

/-!
# The finite Bott model of the height function on the Klein bottle

On the Klein bottle `K = ([0, 1] × S¹) / ((1, e^{iθ}) ∼ (0, e^{-iθ}))`, the height function
`[t, e^{iθ}] ↦ cos θ` is Morse–Bott (`TauCeti.KleinBottle.height`). Its critical set consists of two
circles: the minimum circle `C₀ = {θ = π}`, whose negative normal bundle has rank `0`, and the
maximum circle `C₁ = {θ = 0}`, whose negative normal bundle has rank `1` and is not orientable
(`TauCeti.KleinBottle.isEmpty_vectorBundleOrientation_negativeNormalSpace_criticalCircle_one`):
its orientation line `o(ν⁻_{C₁})` is the rank-one local system on the circle with monodromy `-1`.
The two families of trajectories from `C₁` to `C₀`, one through each open semicircle, are exchanged
at the seam of the mapping torus and contribute opposite signs, so the trajectory correspondence
from `C₁` to `C₀` vanishes. The Bott complex is then the direct sum of the cellular complex of `C₀`
with trivial coefficients and the cellular complex of `C₁` with coefficients in `o(ν⁻_{C₁})`,
shifted by the rank `1`. This file constructs this finite model and computes its homology.

The model is stated for a monodromy `u = ±1` of `o(ν⁻_{C₁})`
(`TauCeti.BottChainData.circleMappingTorus`). The Klein bottle is `u = -1`, the mapping torus of
the reflection `z ↦ conj z` of the circle. The torus, the mapping torus of the identity, with the
same height function `cos θ` and the symmetric metric, is `u = 1`: there the negative line of `C₁`
is trivial and the two trajectory families cancel already on chains.

**Cellular chains.** On each critical circle take one vertex `v` and one positively oriented edge
`e`, with coefficient frames chosen at `v` and along `e`. The cellular chains are `R × R`, the
coefficients of `v` and `e` in degrees `0` and `1` (`TauCeti.circleCellGrading`), and the boundary
of `e` is `ρ(g) v - v = (u - 1) v` (`TauCeti.circleCellBoundary`): `0` for trivial coefficients and
`-2` for the sign local system.

**The Bott differential.** The internal boundary of `C₁` is twisted by `(-1)^1`, so the Bott
differential sends the edge of `C₁` to `(1 - u)` times its vertex
(`TauCeti.BottChainData.differential_circleMappingTorus_apply_one`): for the Klein bottle the
cellular boundary `-2` becomes `+2`. The total-degree pieces of the Bott complex
(`TauCeti.BottChainData.circleMappingTorusComplex`) are `R` in degree `2` (the edge of `C₁`), `R²`
in degree `1` (the edge of `C₀`, then the vertex of `C₁`) and `R` in degree `0` (the vertex of
`C₀`), and zero in every other degree. In these bases it is the finite complex `R → R² → R` with
`d₂(n) = (0, (1 - u) n)` and `d₁ = 0`
(`TauCeti.BottChainData.circleMappingTorusDegreeOneEquiv_d_two_one`,
`TauCeti.BottChainData.circleMappingTorusComplex_d_one_zero`). Hence

* `H₀ = R`,
* `H₁ = R × R ⧸ (1 - u) R`,
* `H₂ = {r : R | (1 - u) r = 0}`,

and the other homology groups vanish. For the Klein bottle over `ℤ` this is `H₀ = ℤ`,
`H₁ = ℤ²/⟨(0, 2)⟩ = ℤ × ℤ/2` and `H₂ = 0`, the integral homology of the Klein bottle
(`TauCeti.BottChainData.nonempty_linearEquiv_homology_circleMappingTorusComplex_singularHomology`).
Replacing the negative line by a trivial line, `u = 1`, would instead give `H₁ = R²` and
`H₂ = R`, the homology of the torus.

Only the model is constructed here. Its identification with the Bott complex of geometric chains
of the height function, the vanishing of the trajectory correspondence for a reflection-invariant
metric, and the comparison of the homology classes of the critical circles with those of `K`
through chain maps are not.

## Main definitions

* `TauCeti.circleCellGrading`, `TauCeti.circleCellBoundary`: the cellular chains of the circle with
  one vertex and one edge, and their boundary with coefficients in a rank-one local system of
  monodromy `u`.
* `TauCeti.BottChainData.circleMappingTorus`: the finite Bott model.
* `TauCeti.BottChainData.circleMappingTorusComplex`: its Bott complex.
* `TauCeti.BottChainData.circleMappingTorusDegreeZeroEquiv`,
  `TauCeti.BottChainData.circleMappingTorusDegreeOneEquiv`,
  `TauCeti.BottChainData.circleMappingTorusDegreeTwoEquiv`: its total-degree pieces in the cellular
  bases.

## Main results

* `TauCeti.BottChainData.circleMappingTorusDegreeOneEquiv_d_two_one`,
  `TauCeti.BottChainData.circleMappingTorusComplex_d_one_zero`,
  `TauCeti.BottChainData.isZero_X_circleMappingTorusComplex`: the comparison with the finite complex
  `R → R² → R`.
* `TauCeti.BottChainData.nonempty_linearEquiv_homology_zero_circleMappingTorusComplex`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_one_circleMappingTorusComplex`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_two_circleMappingTorusComplex`,
  `TauCeti.BottChainData.isZero_homology_circleMappingTorusComplex`: its homology.
* `TauCeti.BottChainData.nonempty_linearEquiv_homology_one_circleMappingTorusComplex_neg_one`,
  `TauCeti.BottChainData.isZero_homology_two_circleMappingTorusComplex_neg_one`: for the Klein
  bottle over `ℤ`, `H₁ = ℤ × ℤ/2` and `H₂ = 0`.
* `TauCeti.BottChainData.nonempty_linearEquiv_homology_circleMappingTorusComplex_singularHomology`:
  in every degree, the homology of the Klein bottle model over `ℤ` is isomorphic to the singular
  homology of the Klein bottle.
* `TauCeti.BottChainData.nonempty_linearEquiv_homology_one_circleMappingTorusComplex_one`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_two_circleMappingTorusComplex_one`: for a
  trivial negative line, `H₁ = R²` and `H₂ = R`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2.4 (the Morse–Bott complex with coefficients in the
  orientation lines of the negative normal bundles) and §6.2.5 (its homology).
* A. Hatcher, *Algebraic Topology*, Section 3.H (homology with local coefficients) and
  Example 2.37 (the homology of the Klein bottle).
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace TauCeti

variable {R : Type*} [Ring R]

/-! ### Cellular chains of the circle with a rank-one local system -/

section CircleCell

variable (R) in
/-- **The grading of the cellular chains of the circle** with one vertex and one edge: in `R × R`,
the first coordinate, the coefficient of the vertex, has degree `0`, and the second, the
coefficient of the edge, has degree `1`. -/
def circleCellGrading (j : ℤ) : Submodule R (R × R) :=
  (if j = 0 then ⊤ else ⊥ : Submodule R R).prod (if j = 1 then ⊤ else ⊥)

/-- A cellular chain of the circle has degree `j` exactly when its vertex coefficient vanishes
unless `j = 0` and its edge coefficient vanishes unless `j = 1`. -/
theorem mem_circleCellGrading_iff {j : ℤ} {x : R × R} :
    x ∈ circleCellGrading R j ↔ (j ≠ 0 → x.1 = 0) ∧ (j ≠ 1 → x.2 = 0) := by
  rw [circleCellGrading, Submodule.mem_prod]
  split_ifs <;> simp_all

variable (R) in
/-- **The cellular boundary of the circle with coefficients in a rank-one local system** of
monodromy `u = ±1`. With one vertex `v`, one positively oriented edge `e` and coefficient frames
chosen at `v` and along `e`, the boundary of `e` is `ρ(g) v - v = (u - 1) v`, and that of `v` is
`0`: on `R × R` it sends `(a, b)` to `((u - 1) b, 0)`. This records the formula for the cellular
differential; its comparison with the twisted cellular complex of the circle is not made here. -/
def circleCellBoundary (u : ℤˣ) : R × R →ₗ[R] R × R :=
  ((u : ℤ) - 1) • (LinearMap.inl R R R ∘ₗ LinearMap.snd R R R)

@[simp]
theorem circleCellBoundary_apply (u : ℤˣ) (x : R × R) :
    circleCellBoundary R u x = (((u : ℤ) - 1) • x.2, 0) := by
  simp only [circleCellBoundary, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.snd_apply,
    LinearMap.inl_apply, Prod.smul_mk, smul_zero]

/-- With trivial coefficients the cellular boundary of the circle vanishes. -/
@[simp]
theorem circleCellBoundary_one : circleCellBoundary R 1 = 0 :=
  LinearMap.ext fun x ↦ by rw [circleCellBoundary_apply, Units.val_one, sub_self, zero_smul]; rfl

/-- The cellular boundary of the circle squares to zero. -/
@[simp]
theorem circleCellBoundary_comp_circleCellBoundary (u : ℤˣ) :
    circleCellBoundary R u ∘ₗ circleCellBoundary R u = 0 :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, circleCellBoundary_apply, circleCellBoundary_apply, smul_zero]; rfl

/-- The cellular boundary of the circle lowers the degree by one. -/
theorem circleCellBoundary_mem_circleCellGrading (u : ℤˣ) {j : ℤ} {x : R × R}
    (hx : x ∈ circleCellGrading R j) : circleCellBoundary R u x ∈ circleCellGrading R (j - 1) := by
  rw [mem_circleCellGrading_iff] at hx ⊢
  exact ⟨fun h ↦ by simp [hx.2 (by omega)], fun _ ↦ by simp⟩

end CircleCell

/-! ### The finite Bott model -/

namespace BottChainData

variable (u : ℤˣ)

variable (R) in
/-- **The finite Bott model of the height function on the Klein bottle**, and more generally on the
mapping torus of a circle map whose maximum circle has a negative line of monodromy `u = ±1`. The
components are the minimum circle `C₀ = 0`, of negative-normal rank `0`, and the maximum circle
`C₁ = 1`, of rank `1`, both of dimension `1`. The chains on each are its cellular chains `R × R`
(vertex, edge), with trivial coefficients on `C₀` and coefficients in the local system of monodromy
`u` on `C₁`, and there are no trajectory correspondences: for the Klein bottle, `u = -1`, the two
trajectory families from `C₁` to `C₀` contribute opposite signs. -/
def circleMappingTorus : BottChainData R (Fin 2) fun _ ↦ R × R :=
  ofBoundary (fun C ↦ (C : ℕ)) (fun _ ↦ 1) ![0, circleCellBoundary R u] fun C ↦ by
    fin_cases C
    · exact LinearMap.zero_comp 0
    · exact circleCellBoundary_comp_circleCellBoundary u

@[simp]
theorem circleMappingTorus_rank : (circleMappingTorus R u).rank = fun C : Fin 2 ↦ (C : ℕ) :=
  ofBoundary_rank ..

@[simp]
theorem circleMappingTorus_dim : (circleMappingTorus R u).dim = fun _ ↦ 1 :=
  ofBoundary_dim ..

/-- The boundary on the minimum circle, with trivial coefficients, vanishes. -/
@[simp]
theorem circleMappingTorus_boundary_zero : (circleMappingTorus R u).boundary 0 = 0 :=
  congrFun (ofBoundary_boundary ..) 0

/-- The boundary on the maximum circle is the cellular boundary with coefficients in the local
system of monodromy `u`. -/
@[simp]
theorem circleMappingTorus_boundary_one :
    (circleMappingTorus R u).boundary 1 = circleCellBoundary R u :=
  congrFun (ofBoundary_boundary ..) 1

@[simp]
theorem circleMappingTorus_pushforward (C D : Fin 2) :
    (circleMappingTorus R u).pushforward C D = 0 :=
  ofBoundary_pushforward ..

/-- The model has no trajectory correspondences. -/
@[simp]
theorem correspondence_circleMappingTorus (C D : Fin 2) :
    (circleMappingTorus R u).correspondence C D = 0 := by
  rw [circleMappingTorus]
  exact correspondence_ofBoundary ..

/-- The Bott differential of the model vanishes on the minimum circle. -/
theorem differential_circleMappingTorus_apply_zero (x : Fin 2 → R × R) :
    (circleMappingTorus R u).differential x 0 = 0 := by
  rw [circleMappingTorus, differential_ofBoundary_apply]
  simp

/-- **The Bott differential on the maximum circle** sends the edge to `(-1)^1 (u - 1) = 1 - u`
times the vertex: for the Klein bottle, `u = -1`, the cellular boundary `-2` becomes `+2` after the
rank-one shift. -/
theorem differential_circleMappingTorus_apply_one (x : Fin 2 → R × R) :
    (circleMappingTorus R u).differential x 1 = ((1 - (u : ℤ)) • (x 1).2, 0) := by
  rw [circleMappingTorus, differential_ofBoundary_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    circleCellBoundary_apply, Fin.val_one, Nat.cast_one, Int.negOnePow_one, Units.neg_smul,
    one_smul, Prod.neg_mk, neg_zero, ← neg_smul, neg_sub]

/-- A chain of the model has total degree `k` exactly when its vertex and edge coefficients on
`C₀`, in chain degrees `0` and `1`, vanish unless `k = 0` and `k = 1`, and those on `C₁`, shifted
by the rank `1`, vanish unless `k = 1` and `k = 2`. -/
theorem mem_totalDegree_circleMappingTorus_iff {k : ℤ} {x : Fin 2 → R × R} :
    x ∈ (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) k ↔
      (k ≠ 0 → (x 0).1 = 0) ∧ (k ≠ 1 → (x 0).2 = 0) ∧ (k ≠ 1 → (x 1).1 = 0) ∧
        (k ≠ 2 → (x 1).2 = 0) := by
  simp only [mem_totalDegree_iff, Fin.forall_fin_two, mem_circleCellGrading_iff,
    circleMappingTorus_rank, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, sub_zero]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨h₁, h₂, fun h ↦ h₃ (by omega), fun h ↦ h₄ (by omega)⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, fun h ↦ h₃ (by omega), fun h ↦ h₄ (by omega)⟩

variable (R) in
/-- **The Bott complex of the finite model**: `R` in total degree `2` (the edge of `C₁`), `R²` in
total degree `1` (the edge of `C₀` and the vertex of `C₁`) and `R` in total degree `0` (the vertex
of `C₀`). -/
@[expose] noncomputable def circleMappingTorusComplex : ChainComplex (ModuleCat R) ℤ :=
  (circleMappingTorus R u).chainComplex (S := fun _ ↦ circleCellGrading R)
    (fun C _ _ hx ↦ by
      fin_cases C
      · simp
      · simpa using circleCellBoundary_mem_circleCellGrading u hx)
    (fun _ _ _ _ _ ↦ by simp)

/-- The differential of the Bott complex of the model is the Bott differential. -/
theorem circleMappingTorusComplex_d_apply {i j : ℤ} (hij : i = j + 1)
    (x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) i) :
    (((circleMappingTorusComplex R u).d i j).hom x :
      (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) j).val =
      (circleMappingTorus R u).differential x.val := by
  subst hij
  exact chainComplex_d_apply _ _ _ _ x

/-! ### The comparison with the finite complex `R → R² → R` -/

/-- The chains of the model of total degree `k ∉ {0, 1, 2}` vanish. -/
theorem eq_zero_of_mem_totalDegree_circleMappingTorus {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1)
    (h2 : k ≠ 2) {x : Fin 2 → R × R}
    (hx : x ∈ (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) k) : x = 0 := by
  obtain ⟨ha, hb, hc, hd⟩ := (mem_totalDegree_circleMappingTorus_iff u).1 hx
  funext C
  fin_cases C
  · exact Prod.ext (ha h0) (hb h1)
  · exact Prod.ext (hc h1) (hd h2)

/-- **The Bott complex of the model vanishes in total degrees other than `0`, `1` and `2`.** -/
theorem isZero_X_circleMappingTorusComplex {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) :
    IsZero ((circleMappingTorusComplex R u).X k) :=
  have : Subsingleton ((circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) k) :=
    ⟨fun x y ↦ Subtype.ext
      ((eq_zero_of_mem_totalDegree_circleMappingTorus u h0 h1 h2 x.property).trans
        (eq_zero_of_mem_totalDegree_circleMappingTorus u h0 h1 h2 y.property).symm)⟩
  ModuleCat.isZero_of_subsingleton (ModuleCat.of R _)

/-- **The chains of total degree `0` of the model** are the multiples of the vertex of the minimum
circle `C₀`. -/
noncomputable def circleMappingTorusDegreeZeroEquiv :
    (circleMappingTorusComplex R u).X 0 ≃ₗ[R] R where
  toFun x := ((x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 0).val 0).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun r := (⟨![(r, 0), 0], (mem_totalDegree_circleMappingTorus_iff u).2 (by simp)⟩ :
    (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 0)
  left_inv x := by
    obtain ⟨-, hb, hc, hd⟩ := (mem_totalDegree_circleMappingTorus_iff u).1
      (x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 0).property
    refine Subtype.ext (funext fun C ↦ ?_)
    fin_cases C
    · exact Prod.ext rfl (hb (by norm_num)).symm
    · exact Prod.ext (hc (by norm_num)).symm (hd (by norm_num)).symm
  right_inv _ := rfl

@[simp]
theorem circleMappingTorusDegreeZeroEquiv_apply (x : (circleMappingTorusComplex R u).X 0) :
    circleMappingTorusDegreeZeroEquiv u x =
      ((x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 0).val 0).1 :=
  (rfl)

theorem coe_circleMappingTorusDegreeZeroEquiv_symm_apply (r : R) :
    ((circleMappingTorusDegreeZeroEquiv u).symm r :
      (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 0).val = ![(r, 0), 0] :=
  (rfl)

/-- **The chains of total degree `1` of the model** are the combinations of the edge of the
minimum circle `C₀` and of the vertex of the maximum circle `C₁`, in this order. -/
noncomputable def circleMappingTorusDegreeOneEquiv :
    (circleMappingTorusComplex R u).X 1 ≃ₗ[R] R × R where
  toFun x :=
    letI y := (x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 1).val
    ((y 0).2, (y 1).1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := (⟨![(0, p.1), (p.2, 0)], (mem_totalDegree_circleMappingTorus_iff u).2 (by simp)⟩ :
    (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 1)
  left_inv x := by
    obtain ⟨ha, -, -, hd⟩ := (mem_totalDegree_circleMappingTorus_iff u).1
      (x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 1).property
    refine Subtype.ext (funext fun C ↦ ?_)
    fin_cases C
    · exact Prod.ext (ha (by norm_num)).symm rfl
    · exact Prod.ext rfl (hd (by norm_num)).symm
  right_inv _ := rfl

@[simp]
theorem circleMappingTorusDegreeOneEquiv_apply (x : (circleMappingTorusComplex R u).X 1) :
    circleMappingTorusDegreeOneEquiv u x =
      (((x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 1).val 0).2,
        ((x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 1).val 1).1) :=
  (rfl)

theorem coe_circleMappingTorusDegreeOneEquiv_symm_apply (p : R × R) :
    ((circleMappingTorusDegreeOneEquiv u).symm p :
      (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 1).val =
      ![(0, p.1), (p.2, 0)] :=
  (rfl)

/-- **The chains of total degree `2` of the model** are the multiples of the edge of the maximum
circle `C₁`. -/
noncomputable def circleMappingTorusDegreeTwoEquiv :
    (circleMappingTorusComplex R u).X 2 ≃ₗ[R] R where
  toFun x := ((x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 2).val 1).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun r := (⟨![0, (0, r)], (mem_totalDegree_circleMappingTorus_iff u).2 (by simp)⟩ :
    (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 2)
  left_inv x := by
    obtain ⟨ha, hb, hc, -⟩ := (mem_totalDegree_circleMappingTorus_iff u).1
      (x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 2).property
    refine Subtype.ext (funext fun C ↦ ?_)
    fin_cases C
    · exact Prod.ext (ha (by norm_num)).symm (hb (by norm_num)).symm
    · exact Prod.ext (hc (by norm_num)).symm rfl
  right_inv _ := rfl

@[simp]
theorem circleMappingTorusDegreeTwoEquiv_apply (x : (circleMappingTorusComplex R u).X 2) :
    circleMappingTorusDegreeTwoEquiv u x =
      ((x : (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 2).val 1).2 :=
  (rfl)

theorem coe_circleMappingTorusDegreeTwoEquiv_symm_apply (r : R) :
    ((circleMappingTorusDegreeTwoEquiv u).symm r :
      (circleMappingTorus R u).totalDegree (fun _ ↦ circleCellGrading R) 2).val = ![0, (0, r)] :=
  (rfl)

/-- **The differential `d₂` of the model** is `n ↦ (0, (1 - u) n)` in the cellular bases: it sends
the edge of `C₁` to `1 - u` times the vertex of `C₁`, and misses the edge of `C₀`. For the Klein
bottle, `u = -1`, it is `n ↦ (0, 2 n)`. -/
theorem circleMappingTorusDegreeOneEquiv_d_two_one (x : (circleMappingTorusComplex R u).X 2) :
    circleMappingTorusDegreeOneEquiv u (((circleMappingTorusComplex R u).d 2 1).hom x) =
      (0, (1 - (u : ℤ)) • circleMappingTorusDegreeTwoEquiv u x) := by
  rw [circleMappingTorusDegreeOneEquiv_apply, circleMappingTorusDegreeTwoEquiv_apply,
    circleMappingTorusComplex_d_apply (R := R) u (by norm_num : (2 : ℤ) = 1 + 1) x,
    differential_circleMappingTorus_apply_zero, differential_circleMappingTorus_apply_one]
  rfl

/-- **The differential `d₁` of the model vanishes**: the edge of `C₀` has trivial coefficients
and the vertex of `C₁` is a cycle. -/
theorem circleMappingTorusComplex_d_one_zero : (circleMappingTorusComplex R u).d 1 0 = 0 := by
  ext x : 2
  refine Subtype.ext ((circleMappingTorusComplex_d_apply u (by norm_num) x).trans ?_)
  obtain ⟨-, -, -, hd⟩ := (mem_totalDegree_circleMappingTorus_iff u).1 x.property
  funext C
  fin_cases C
  · exact differential_circleMappingTorus_apply_zero u _
  · rw [Fin.mk_one, differential_circleMappingTorus_apply_one, hd (by norm_num), smul_zero]
    rfl

/-! ### Homology -/

/-- The differential of the model out of total degree `0` vanishes: nothing has degree `-1`. -/
private theorem circleMappingTorusComplex_d_zero_neg_one :
    (circleMappingTorusComplex R u).d 0 (-1) = 0 :=
  (isZero_X_circleMappingTorusComplex u (by norm_num) (by norm_num) (by norm_num)).eq_of_tgt _ _

/-- The differential of the model into total degree `2` vanishes: nothing has degree `3`. -/
private theorem circleMappingTorusComplex_d_three_two :
    (circleMappingTorusComplex R u).d 3 2 = 0 :=
  (isZero_X_circleMappingTorusComplex u (by norm_num) (by norm_num) (by norm_num)).eq_of_src _ _

variable (R) in
/-- **`H₀ = R` for the model**, spanned by the vertex of the minimum circle. -/
theorem nonempty_linearEquiv_homology_zero_circleMappingTorusComplex :
    Nonempty ((circleMappingTorusComplex R u).homology 0 ≃ₗ[R] R) :=
  (circleMappingTorusComplex R u).nonempty_linearEquiv_homology_of_surjective (i := 1) (k := -1)
    (by simp) (by simp)
    ((circleMappingTorusDegreeZeroEquiv u).toLinearMap ∘ₗ
      (LinearMap.ker ((circleMappingTorusComplex R u).d 0 (-1)).hom).subtype)
    (fun r ↦ ⟨⟨(circleMappingTorusDegreeZeroEquiv u).symm r, by
      rw [LinearMap.mem_ker, circleMappingTorusComplex_d_zero_neg_one]
      rfl⟩, (circleMappingTorusDegreeZeroEquiv u).apply_symm_apply r⟩)
    (fun z ↦ by
      rw [circleMappingTorusComplex_d_one_zero, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff, Submodule.subtype_apply, Submodule.coe_eq_zero]
      simp [eq_comm])

variable (R) in
/-- **`H₁ = R × R ⧸ (1 - u) R` for the model.** Every chain of total degree `1` is a cycle, and
the boundaries are the multiples of `1 - u` times the vertex of `C₁`; the first factor is spanned
by the edge of `C₀`. -/
theorem nonempty_linearEquiv_homology_one_circleMappingTorusComplex :
    Nonempty ((circleMappingTorusComplex R u).homology 1 ≃ₗ[R]
      R × (R ⧸ LinearMap.range ((1 - (u : ℤ)) • LinearMap.id : R →ₗ[R] R))) := by
  set N := LinearMap.range ((1 - (u : ℤ)) • LinearMap.id : R →ₗ[R] R)
  refine (circleMappingTorusComplex R u).nonempty_linearEquiv_homology_of_surjective (i := 2)
    (k := 0) (by simp) (by simp)
    ((LinearMap.id.prodMap N.mkQ) ∘ₗ (circleMappingTorusDegreeOneEquiv u).toLinearMap ∘ₗ
      (LinearMap.ker ((circleMappingTorusComplex R u).d 1 0).hom).subtype) ?_ ?_
  · rintro ⟨a, q⟩
    obtain ⟨b, rfl⟩ := N.mkQ_surjective q
    refine ⟨⟨(circleMappingTorusDegreeOneEquiv u).symm (a, b), by
      rw [LinearMap.mem_ker, circleMappingTorusComplex_d_one_zero]
      rfl⟩, ?_⟩
    simp
  · intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      LinearMap.prodMap_apply, LinearMap.id_apply, Prod.mk_eq_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨h₁, r, hr⟩
      refine ⟨(circleMappingTorusDegreeTwoEquiv u).symm r,
        (circleMappingTorusDegreeOneEquiv u).injective ?_⟩
      rw [circleMappingTorusDegreeOneEquiv_d_two_one, LinearEquiv.apply_symm_apply]
      exact Prod.ext h₁.symm hr
    · rintro ⟨y, hy⟩
      rw [← hy, circleMappingTorusDegreeOneEquiv_d_two_one]
      exact ⟨rfl, _, rfl⟩

variable (R) in
/-- **`H₂ = {r | (1 - u) r = 0}` for the model.** Nothing has total degree `3`, and a multiple `r`
of the edge of `C₁` is a cycle exactly when `(1 - u) r = 0`. -/
theorem nonempty_linearEquiv_homology_two_circleMappingTorusComplex :
    Nonempty ((circleMappingTorusComplex R u).homology 2 ≃ₗ[R]
      LinearMap.ker ((1 - (u : ℤ)) • LinearMap.id : R →ₗ[R] R)) := by
  have hcyc (x : (circleMappingTorusComplex R u).X 2) :
      x ∈ LinearMap.ker ((circleMappingTorusComplex R u).d 2 1).hom ↔
        circleMappingTorusDegreeTwoEquiv u x ∈
          LinearMap.ker ((1 - (u : ℤ)) • LinearMap.id : R →ₗ[R] R) := by
    rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
      ← (circleMappingTorusDegreeOneEquiv u).map_eq_zero_iff,
      circleMappingTorusDegreeOneEquiv_d_two_one, Prod.mk_eq_zero]
    exact and_iff_right rfl
  refine (circleMappingTorusComplex R u).nonempty_linearEquiv_homology_of_surjective (i := 3)
    (k := 1) (by simp) (by simp)
    ((circleMappingTorusDegreeTwoEquiv u).toLinearMap.restrict fun x hx ↦ by
      rw [LinearEquiv.coe_coe]
      exact (hcyc x).1 hx) ?_ ?_
  · rintro ⟨r, hr⟩
    refine ⟨⟨(circleMappingTorusDegreeTwoEquiv u).symm r, (hcyc _).2 ?_⟩, Subtype.ext ?_⟩
    · rwa [LinearEquiv.apply_symm_apply]
    · exact (circleMappingTorusDegreeTwoEquiv u).apply_symm_apply r
  · intro z
    rw [circleMappingTorusComplex_d_three_two]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, Subtype.ext_iff,
      ZeroMemClass.coe_zero]
    rw [LinearMap.coe_restrict_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
    exact eq_comm

/-- **The other homology groups of the model vanish.** -/
theorem isZero_homology_circleMappingTorusComplex {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) :
    IsZero ((circleMappingTorusComplex R u).homology k) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_X_circleMappingTorusComplex u h0 h1 h2)

/-! ### The Klein bottle and the trivial line -/

/-- Over `ℤ`, the multiples of `1 - (-1) = 2` form the ideal generated by `2`. -/
private theorem range_one_sub_neg_one_smul_id :
    LinearMap.range ((1 - ((-1 : ℤˣ) : ℤ)) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) =
      Ideal.span {((2 : ℕ) : ℤ)} := by
  ext n
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp⟩

/-- **`H₁ = ℤ × ℤ/2` for the Klein bottle model over `ℤ`**: the edge of `C₀` spans the free summand,
and the vertex of `C₁` is a cycle whose double is the boundary of the edge of `C₁`. -/
theorem nonempty_linearEquiv_homology_one_circleMappingTorusComplex_neg_one :
    Nonempty ((circleMappingTorusComplex ℤ (-1)).homology 1 ≃ₗ[ℤ] ℤ × ZMod 2) :=
  let ⟨e⟩ := nonempty_linearEquiv_homology_one_circleMappingTorusComplex ℤ (-1)
  ⟨e ≪≫ₗ (LinearEquiv.refl ℤ ℤ).prodCongr (Submodule.quotEquivOfEq _ _
    range_one_sub_neg_one_smul_id ≪≫ₗ (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv)⟩

/-- **`H₂ = 0` for the Klein bottle model over `ℤ`**: the edge of `C₁` has boundary twice the
vertex of `C₁`, and `2 n = 0` forces `n = 0` in `ℤ`. -/
theorem isZero_homology_two_circleMappingTorusComplex_neg_one :
    IsZero ((circleMappingTorusComplex ℤ (-1)).homology 2) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_two_circleMappingTorusComplex ℤ (-1)
  have : Subsingleton (LinearMap.ker ((1 - ((-1 : ℤˣ) : ℤ)) • LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := by
    refine ⟨fun a b ↦ Subtype.ext ?_⟩
    have ha := LinearMap.mem_ker.1 a.property
    have hb := LinearMap.mem_ker.1 b.property
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Units.val_neg, Units.val_one,
      smul_eq_mul] at ha hb
    omega
  have := e.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- **The Klein bottle model has the integral homology of the Klein bottle**: in every degree its
homology over `ℤ` is isomorphic to the singular homology of `K`, namely `ℤ`, `ℤ × ℤ/2` and `0` in
degrees `0`, `1` and `≥ 2`. The isomorphisms are abstract: they are not induced by chain maps
between the model and singular chains. -/
theorem nonempty_linearEquiv_homology_circleMappingTorusComplex_singularHomology
    (k : ℕ) :
    Nonempty ((circleMappingTorusComplex ℤ (-1)).homology k ≃ₗ[ℤ]
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of KleinBottle)) := by
  match k with
  | 0 =>
    obtain ⟨e⟩ := nonempty_linearEquiv_homology_zero_circleMappingTorusComplex ℤ (-1)
    exact ⟨e ≪≫ₗ KleinBottle.singularHomologyZeroLinearEquiv.symm⟩
  | 1 =>
    obtain ⟨e⟩ := nonempty_linearEquiv_homology_one_circleMappingTorusComplex_neg_one
    exact ⟨e ≪≫ₗ KleinBottle.singularHomologyOneLinearEquiv.symm⟩
  | n + 2 =>
    refine ⟨(IsZero.iso ?_
      (KleinBottle.isZero_singularHomology_of_two_le (by omega))).toLinearEquiv⟩
    rcases n with _ | n
    · exact isZero_homology_two_circleMappingTorusComplex_neg_one
    · exact isZero_homology_circleMappingTorusComplex _ (by omega) (by omega) (by omega)

/-- **For a trivial negative line, `H₁ = R²`**: the differential `d₂` vanishes. This is the case of
the torus, and it shows that the summand `ℤ/2` of the Klein bottle comes from the monodromy `-1` of
the negative line of `C₁`. -/
theorem nonempty_linearEquiv_homology_one_circleMappingTorusComplex_one :
    Nonempty ((circleMappingTorusComplex R 1).homology 1 ≃ₗ[R] R × R) :=
  let ⟨e⟩ := nonempty_linearEquiv_homology_one_circleMappingTorusComplex R 1
  ⟨e ≪≫ₗ (LinearEquiv.refl R R).prodCongr (Submodule.quotEquivOfEqBot _ (by simp))⟩

/-- **For a trivial negative line, `H₂ = R`**, spanned by the edge of `C₁`: the fundamental class
of the torus. -/
theorem nonempty_linearEquiv_homology_two_circleMappingTorusComplex_one :
    Nonempty ((circleMappingTorusComplex R 1).homology 2 ≃ₗ[R] R) :=
  let ⟨e⟩ := nonempty_linearEquiv_homology_two_circleMappingTorusComplex R 1
  ⟨e ≪≫ₗ LinearEquiv.ofTop _ (by simp)⟩

end BottChainData

end TauCeti
