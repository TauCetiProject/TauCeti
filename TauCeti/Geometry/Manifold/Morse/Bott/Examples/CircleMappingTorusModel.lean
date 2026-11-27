/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Complex
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.KleinBottle
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Tactic.DeriveFintype

/-!
# The cellular Bott models of the height on the torus and on the Klein bottle

Let `K_ε = (ℝ × S¹) / ((t + 1, z) ∼ (t, φ z))` be the mapping torus of the identity `φ = id`
(`ε = 1`, the torus) or of complex conjugation `φ = conj` (`ε = -1`, the Klein bottle
`TauCeti.KleinBottle`), with the height `[t, e^{iθ}] ↦ cos θ` (`TauCeti.KleinBottle.height`). Its
critical set consists of two circles: the minimum circle `C₀ = {θ = π}`, whose negative normal
bundle has rank `0`, and the maximum circle `C₁ = {θ = 0}`, whose negative normal bundle is a line,
with orientation monodromy `ε` around `C₁`; for the Klein bottle it is the Möbius line
(`TauCeti.KleinBottle.isEmpty_vectorBundleOrientation_negativeNormalSpace_criticalCircle_one`).
For a reflection-invariant product metric the trajectories from `C₁` to `C₀` come in two families,
the two open semicircles, whose signed endpoint contributions cancel. This file works out the Bott
complex (`TauCeti.BottChainData`) of this function when the chains on each critical circle are its
cellular chains with coefficients in the orientation line of its negative normal bundle.

**The sign circle.** The circle with one vertex and one edge, with coefficients in the rank-one
local system of monodromy `ε = ±1`, has the cellular chains `R × R` (vertex coefficient, edge
coefficient), graded by `TauCeti.circleCellularGrading`, and the boundary
`∂ (a, b) = ((ε - 1) b, 0)` (`TauCeti.circleCellularBoundary`): the coefficient of the edge
transported once around the circle, minus that coefficient. For trivial coefficients the edge is a
cycle, while for the sign system its boundary is `-2` times the vertex.

**The model.** `TauCeti.BottChainData.circleMappingTorus R ε` has the two critical circles
`TauCeti.CircleMappingTorusComponent`, with cellular chains of trivial coefficients on `C₀` and of
monodromy `ε` on `C₁`, and no correspondence. Its Bott complex
`TauCeti.BottChainData.circleMappingTorusComplex R ε` is the cellular complex of `C₀` plus the
cellular complex of `C₁` shifted up by the rank `1`, whose internal boundary `-∂` sends the edge to
`(1 - ε)` times the vertex (`TauCeti.BottChainData.differential_circleMappingTorus_maxCircle`): for
the Klein bottle the boundary `-2` becomes `+2`. In the bases `(edge of C₁)`,
`(edge of C₀, vertex of C₁)`, `(vertex of C₀)` of total degrees `2, 1, 0` this is the complex
`R → R² → R` with `d₂ n = (0, (1 - ε) n)` and `d₁ = 0`. Its homology is
(`TauCeti.BottChainData.nonempty_linearEquiv_homology_zero_circleMappingTorusComplex` and the
following theorems)

* `H₀ = R`, the vertex of `C₀`;
* `H₁ = R × R ⧸ (1 - ε)`, the edge of `C₀` and the vertex of `C₁` modulo `1 - ε`;
* `H₂ = {n ∈ R | (1 - ε) n = 0}`, and `Hₖ = 0` in all other degrees.

For the torus this is `R, R², R`, the homology of `T²`
(`TauCeti.BottChainData.nonempty_linearEquiv_homology_one_circleMappingTorusComplex_one`,
`TauCeti.BottChainData.nonempty_linearEquiv_homology_two_circleMappingTorusComplex_one`). For the
Klein bottle over `ℤ` it is `ℤ, ℤ × ℤ/2, 0`
(`TauCeti.BottChainData.nonempty_linearEquiv_homology_one_circleMappingTorusComplex_neg_one`,
`TauCeti.BottChainData.isZero_homology_two_circleMappingTorusComplex_neg_one`): replacing the Möbius
line by a trivial line would give `ℤ²` instead of `ℤ × ℤ/2`. These groups agree, degree by degree,
with the singular homology of the Klein bottle computed from its Wang sequence
(`TauCeti.BottChainData.nonempty_linearEquiv_homology_circleMappingTorusComplex_kleinBottle`).
This comparison goes through the computed groups; no chain map between the two complexes is
constructed here, and the reduction of the Bott complex of geometric chains to this cellular model
is not formalized.

## Main definitions

* `TauCeti.circleCellularBoundary`, `TauCeti.circleCellularGrading`: the cellular chains of the
  circle with coefficients in a rank-one local system of monodromy `±1`.
* `TauCeti.CircleMappingTorusComponent`: the two critical circles of the height.
* `TauCeti.BottChainData.circleMappingTorus`, `TauCeti.BottChainData.circleMappingTorusComplex`:
  the cellular Bott model and its Bott complex.

## Main results

* `TauCeti.BottChainData.differential_circleMappingTorus_maxCircle`: the shifted internal boundary
  of the maximum circle.
* `TauCeti.BottChainData.nonempty_linearEquiv_homology_zero_circleMappingTorusComplex`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_one_circleMappingTorusComplex`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_two_circleMappingTorusComplex`,
  `TauCeti.BottChainData.isZero_homology_circleMappingTorusComplex`: the homology of the model.
* `TauCeti.BottChainData.nonempty_linearEquiv_homology_circleMappingTorusComplex_kleinBottle`: for
  the Klein bottle over `ℤ` the homology of the model is that of the Klein bottle.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2.4 (the Morse–Bott complex with orientation local systems)
  and §6.2.5 (its homology).
* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.37 (the homology of the Klein bottle)
  and Section 3.H (homology with local coefficients).
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace TauCeti

/-! ### The cellular chains of the circle with a rank-one local system -/

section CircleCellular

variable (R : Type*) [Ring R]

/-- **The cellular boundary of the circle with coefficients in a rank-one local system** of
monodromy `ε = ±1`. The circle has one vertex and one edge from the vertex to itself; a chain is a
pair `(a, b)` of a vertex coefficient `a` and an edge coefficient `b`, and the boundary of the edge
is its coefficient transported once around the circle minus its coefficient at the start:
`∂ (a, b) = ((ε - 1) b, 0)`. -/
def circleCellularBoundary (ε : ℤˣ) : R × R →ₗ[R] R × R :=
  LinearMap.inl R R R ∘ₗ (((ε : ℤ) - 1) • LinearMap.snd R R R)

/-- **The grading of the cellular chains of the circle**: the vertex coefficient has degree `0`
and the edge coefficient degree `1`. -/
def circleCellularGrading (j : ℤ) : Submodule R (R × R) :=
  Submodule.prod (if j = 0 then ⊤ else ⊥) (if j = 1 then ⊤ else ⊥)

variable {R}

@[simp]
theorem circleCellularBoundary_apply (ε : ℤˣ) (x : R × R) :
    circleCellularBoundary R ε x = (((ε : ℤ) - 1) • x.2, 0) := by
  simp [circleCellularBoundary]

@[simp]
theorem circleCellularBoundary_comp_self (ε : ℤˣ) :
    circleCellularBoundary R ε ∘ₗ circleCellularBoundary R ε = 0 :=
  LinearMap.ext fun x ↦ by simp

/-- With trivial coefficients the edge of the circle is a cycle. -/
@[simp]
theorem circleCellularBoundary_one : circleCellularBoundary R 1 = 0 :=
  LinearMap.ext fun x ↦ by simp

/-- **The boundary of the sign circle**: with coefficients of monodromy `-1`, the boundary of the
edge is `-2` times the vertex. -/
theorem circleCellularBoundary_neg_one_apply (x : R × R) :
    circleCellularBoundary R (-1) x = ((-2 : ℤ) • x.2, 0) := by
  simp only [circleCellularBoundary_apply, Units.val_neg, Units.val_one]
  norm_num

theorem mem_circleCellularGrading_iff {j : ℤ} {x : R × R} :
    x ∈ circleCellularGrading R j ↔ (j ≠ 0 → x.1 = 0) ∧ (j ≠ 1 → x.2 = 0) := by
  unfold circleCellularGrading
  by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp_all [Prod.ext_iff]

/-- The cellular boundary of the circle lowers the degree by one. -/
theorem circleCellularBoundary_mem (ε : ℤˣ) {j : ℤ} {x : R × R}
    (hx : x ∈ circleCellularGrading R j) :
    circleCellularBoundary R ε x ∈ circleCellularGrading R (j - 1) := by
  rw [mem_circleCellularGrading_iff] at hx ⊢
  simp only [circleCellularBoundary_apply, ne_eq, implies_true, and_true]
  intro hj
  rw [hx.2 (by omega), smul_zero]

end CircleCellular

/-! ### The two critical circles -/

/-- **The critical circles of the height** `[t, e^{iθ}] ↦ cos θ` on the torus or the Klein bottle:
the minimum circle `C₀ = {θ = π}` and the maximum circle `C₁ = {θ = 0}`. -/
inductive CircleMappingTorusComponent
  | minCircle
  | maxCircle
  deriving DecidableEq, Fintype

namespace CircleMappingTorusComponent

/-- The negative-normal ranks `λ_C` of the two critical circles: `0` for the minimum and `1` for the
maximum. -/
abbrev rank : CircleMappingTorusComponent → ℕ
  | minCircle => 0
  | maxCircle => 1

end CircleMappingTorusComponent

/-! ### The cellular Bott model -/

namespace BottChainData

open CircleMappingTorusComponent

variable {R : Type*} [Ring R] (ε : ℤˣ)

variable (R) in
/-- **The cellular Bott model of the height on the torus (`ε = 1`) or the Klein bottle
(`ε = -1`).** The chains on each critical circle are its cellular chains, with trivial coefficients
on the minimum circle and coefficients of monodromy `ε`, the orientation line of the negative
normal line, on the maximum circle. There is no correspondence: the two families of trajectories
from the maximum to the minimum circle have opposite signed endpoint contributions. -/
def circleMappingTorus : BottChainData R CircleMappingTorusComponent fun _ ↦ R × R :=
  ofBoundary CircleMappingTorusComponent.rank (fun _ ↦ 1)
    (fun C ↦ circleCellularBoundary R (if C = maxCircle then ε else 1))
    (fun _ ↦ circleCellularBoundary_comp_self _)

@[simp]
theorem circleMappingTorus_rank :
    (circleMappingTorus R ε).rank = CircleMappingTorusComponent.rank :=
  ofBoundary_rank ..

@[simp]
theorem circleMappingTorus_dim : (circleMappingTorus R ε).dim = fun _ ↦ 1 :=
  ofBoundary_dim ..

@[simp]
theorem circleMappingTorus_boundary_minCircle :
    (circleMappingTorus R ε).boundary minCircle = 0 := by
  simp [circleMappingTorus]

@[simp]
theorem circleMappingTorus_boundary_maxCircle :
    (circleMappingTorus R ε).boundary maxCircle = circleCellularBoundary R ε := by
  simp [circleMappingTorus]

@[simp]
theorem circleMappingTorus_pushforward (C D : CircleMappingTorusComponent) :
    (circleMappingTorus R ε).pushforward C D = 0 :=
  ofBoundary_pushforward ..

@[simp]
theorem correspondence_circleMappingTorus (C D : CircleMappingTorusComponent) :
    (circleMappingTorus R ε).correspondence C D = 0 := by
  rw [circleMappingTorus, correspondence_ofBoundary]

/-- The Bott differential of the model vanishes on the minimum circle: the boundary of its cellular
chains with trivial coefficients vanishes, and there are no correspondences. -/
theorem differential_circleMappingTorus_minCircle (x : CircleMappingTorusComponent → R × R) :
    (circleMappingTorus R ε).differential x minCircle = 0 := by
  rw [circleMappingTorus, differential_ofBoundary_apply]
  simp

/-- **The shifted boundary of the maximum circle**: the Bott differential on the maximum circle
is its internal boundary `(-1)^1 ∂`, which sends the edge to `(1 - ε)` times the vertex. -/
theorem differential_circleMappingTorus_maxCircle (x : CircleMappingTorusComponent → R × R) :
    (circleMappingTorus R ε).differential x maxCircle = ((1 - (ε : ℤ)) • (x maxCircle).2, 0) := by
  rw [circleMappingTorus, differential_ofBoundary_apply]
  simp only [CircleMappingTorusComponent.rank, Nat.cast_one, Int.negOnePow_one, ite_true,
    circleCellularBoundary_apply, Units.neg_smul, one_smul, Prod.neg_mk, neg_zero, ← neg_smul,
    neg_sub]

/-- **The rank-one shift turns `-2` into `+2`**: for the Klein bottle, the Bott differential sends
the edge of the maximum circle to twice its vertex. -/
theorem differential_circleMappingTorus_neg_one_maxCircle
    (x : CircleMappingTorusComponent → R × R) :
    (circleMappingTorus R (-1)).differential x maxCircle = ((2 : ℤ) • (x maxCircle).2, 0) := by
  rw [differential_circleMappingTorus_maxCircle]
  norm_num

/-- A chain of the model has total degree `k` exactly when its vertex coefficient on the minimum
circle vanishes unless `k = 0`, its edge coefficient on the minimum circle and vertex coefficient
on the maximum circle vanish unless `k = 1`, and its edge coefficient on the maximum circle
vanishes unless `k = 2`. -/
theorem mem_totalDegree_circleMappingTorus_iff {k : ℤ} {x : CircleMappingTorusComponent → R × R} :
    x ∈ (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) k ↔
      (k ≠ 0 → (x minCircle).1 = 0) ∧ (k ≠ 1 → (x minCircle).2 = 0) ∧
        (k ≠ 1 → (x maxCircle).1 = 0) ∧ (k ≠ 2 → (x maxCircle).2 = 0) := by
  simp only [mem_totalDegree_iff, circleMappingTorus_rank, mem_circleCellularGrading_iff]
  constructor
  · intro h
    have h₀ := h minCircle
    have h₁ := h maxCircle
    simp only [CircleMappingTorusComponent.rank, Nat.cast_zero, sub_zero, Nat.cast_one] at h₀ h₁
    exact ⟨h₀.1, h₀.2, fun hk ↦ h₁.1 (by omega), fun hk ↦ h₁.2 (by omega)⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩ C
    cases C
    · simpa using ⟨h₁, h₂⟩
    · exact ⟨fun hk ↦ h₃ (by simp at hk; omega), fun hk ↦ h₄ (by simp at hk; omega)⟩

/-- The pushforwards of the model, all zero, shift the cellular grading by any amount. -/
theorem circleMappingTorus_pushforward_mem (C D : CircleMappingTorusComponent) (j : ℤ) (x : R × R)
    (_ : x ∈ circleCellularGrading R j) :
    (circleMappingTorus R ε).pushforward C D x ∈
      circleCellularGrading R (j + bottDegreeShift (circleMappingTorus R ε).rank C D) := by
  simp only [circleMappingTorus_pushforward, LinearMap.zero_apply]
  exact zero_mem _

variable (R) in
/-- **The Bott complex of the cellular model** of the height on the torus (`ε = 1`) or the Klein
bottle (`ε = -1`): the cellular complex of the minimum circle plus that of the maximum circle,
shifted up by one. -/
@[expose] noncomputable def circleMappingTorusComplex : ChainComplex (ModuleCat R) ℤ :=
  (circleMappingTorus R ε).chainComplex (S := fun _ ↦ circleCellularGrading R)
    (fun C _ _ hx ↦ by
      cases C
      · simp only [circleMappingTorus_boundary_minCircle, LinearMap.zero_apply]
        exact zero_mem _
      · simpa using circleCellularBoundary_mem ε hx)
    (circleMappingTorus_pushforward_mem ε)

/-- The differential of the Bott complex of the model is the Bott differential. -/
theorem circleMappingTorusComplex_d_apply {i j : ℤ} (hij : i = j + 1)
    (x : (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) i) :
    (((circleMappingTorusComplex R ε).d i j).hom x :
        (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) j).val =
      (circleMappingTorus R ε).differential x.val := by
  subst hij
  exact chainComplex_d_apply _ _ _ _ x

/-- The homology of the model in degree `k` is computed by a linear map `ψ` on the chains of
total degree `k`: if `ψ` maps the cycles onto a submodule `P`, and its kernel on the cycles
consists of the boundaries, then the homology in degree `k` is `P`. -/
private theorem nonempty_linearEquiv_homology_of_cycles {k : ℤ} {N : Type*} [AddCommGroup N]
    [Module R N] (ψ : (CircleMappingTorusComponent → R × R) →ₗ[R] N) (P : Submodule R N)
    (hmem : ∀ x ∈ (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) k,
      (circleMappingTorus R ε).differential x = 0 → ψ x ∈ P)
    (hψ : ∀ n ∈ P, ∃ x ∈ (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) k,
      (circleMappingTorus R ε).differential x = 0 ∧ ψ x = n)
    (hker : ∀ x ∈ (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) k,
      (circleMappingTorus R ε).differential x = 0 → ψ x = 0 →
        ∃ y ∈ (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) (k + 1),
          (circleMappingTorus R ε).differential y = x)
    (hbd : ∀ y ∈ (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) (k + 1),
      ψ ((circleMappingTorus R ε).differential y) = 0) :
    Nonempty ((circleMappingTorusComplex R ε).homology k ≃ₗ[R] P) := by
  let K := circleMappingTorusComplex R ε
  have hcyc (x : (circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) k) :
      (K.d k (k - 1)).hom x = 0 ↔ (circleMappingTorus R ε).differential x.val = 0 := by
    rw [← circleMappingTorusComplex_d_apply ε (j := k - 1) (by ring) x]
    exact Submodule.coe_eq_zero.symm
  -- `ψ` read on the cycles of `K` in degree `k`, with values in `P`
  let ψ' : LinearMap.ker (K.d k (k - 1)).hom →ₗ[R] P :=
    (ψ ∘ₗ ((circleMappingTorus R ε).totalDegree (fun _ ↦ circleCellularGrading R) k).subtype ∘ₗ
      (LinearMap.ker (K.d k (k - 1)).hom).subtype).codRestrict P
      fun x ↦ hmem x.val.val x.val.property ((hcyc x.val).1 x.property)
  have hψ' : Function.Surjective ψ' := by
    rintro ⟨n, hn⟩
    obtain ⟨x, hx, hdx, rfl⟩ := hψ n hn
    exact ⟨⟨⟨x, hx⟩, (hcyc ⟨x, hx⟩).2 hdx⟩, rfl⟩
  have hrange : LinearMap.range (K.sc' (k + 1) k (k - 1)).moduleCatToCycles = LinearMap.ker ψ' := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨y, hy⟩, rfl⟩
      exact Subtype.ext ((congrArg ψ (circleMappingTorusComplex_d_apply ε rfl ⟨y, hy⟩)).trans
        (hbd y hy))
    · rintro ⟨⟨x, hx⟩, hdx⟩ hz
      obtain ⟨y, hy, rfl⟩ := hker x hx ((hcyc ⟨x, hx⟩).1 hdx) (congrArg Subtype.val hz)
      exact ⟨⟨y, hy⟩, Subtype.ext (Subtype.ext (circleMappingTorusComplex_d_apply ε rfl ⟨y, hy⟩))⟩
  exact ⟨(K.homologyIsoSc' (k + 1) k (k - 1) (by simp) (by simp) ≪≫
    (K.sc' (k + 1) k (k - 1)).moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hrange ≪≫ₗ ψ'.quotKerEquivOfSurjective hψ'⟩

/-- **`H₀ = R` for the model**, spanned by the vertex of the minimum circle. -/
theorem nonempty_linearEquiv_homology_zero_circleMappingTorusComplex :
    Nonempty ((circleMappingTorusComplex R ε).homology 0 ≃ₗ[R] R) := by
  refine (nonempty_linearEquiv_homology_of_cycles ε
    (LinearMap.fst R R R ∘ₗ LinearMap.proj minCircle) ⊤ (fun _ _ _ ↦ Submodule.mem_top)
    (fun r _ ↦ ?_) (fun x hx _ hz ↦ ?_) (fun y _ ↦ by simp)).map
      fun e ↦ e ≪≫ₗ LinearEquiv.ofTop ⊤ rfl
  · refine ⟨Pi.single minCircle (r, 0), ?_, ?_, by simp⟩
    · rw [mem_totalDegree_circleMappingTorus_iff]
      simp
    · funext C
      cases C <;> simp
  · rw [mem_totalDegree_circleMappingTorus_iff] at hx
    refine ⟨0, zero_mem _, (map_zero _).trans (funext fun C ↦ ?_)⟩
    cases C
    · exact Prod.ext hz.symm (hx.2.1 (by simp)).symm
    · exact Prod.ext (hx.2.2.1 (by simp)).symm (hx.2.2.2 (by simp)).symm

/-- **`H₁ = R × R ⧸ (1 - ε)` for the model**: the edge of the minimum circle is a cycle, and the
vertex of the maximum circle is a cycle whose multiples by `1 - ε` bound. -/
theorem nonempty_linearEquiv_homology_one_circleMappingTorusComplex :
    Nonempty ((circleMappingTorusComplex R ε).homology 1 ≃ₗ[R]
      R × (R ⧸ Submodule.span R {((1 - (ε : ℤ) : ℤ) : R)})) := by
  set c : R := ((1 - (ε : ℤ) : ℤ) : R)
  have hspan (r : R) : r ∈ Submodule.span R {c} ↔ ∃ n : R, (1 - (ε : ℤ)) • n = r := by
    simp only [Submodule.mem_span_singleton, smul_eq_mul, zsmul_eq_mul, c, Int.cast_comm]
  refine (nonempty_linearEquiv_homology_of_cycles ε
    ((LinearMap.snd R R R ∘ₗ LinearMap.proj minCircle).prod
      ((Submodule.span R {c}).mkQ ∘ₗ LinearMap.fst R R R ∘ₗ LinearMap.proj maxCircle)) ⊤
    (fun _ _ _ ↦ Submodule.mem_top) (fun ⟨a, b⟩ _ ↦ ?_) (fun x hx _ hz ↦ ?_) (fun y _ ↦ ?_)).map
      fun e ↦ e ≪≫ₗ LinearEquiv.ofTop ⊤ rfl
  · obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
    refine ⟨fun C ↦ if C = minCircle then (0, a) else (b, 0), ?_, ?_, by simp⟩
    · rw [mem_totalDegree_circleMappingTorus_iff]
      simp
    · funext C
      cases C <;> simp
  · rw [mem_totalDegree_circleMappingTorus_iff] at hx
    have hmin : (x minCircle).2 = 0 := congrArg Prod.fst hz
    have hmax : (Submodule.span R {c}).mkQ (x maxCircle).1 = 0 := congrArg Prod.snd hz
    obtain ⟨n, hn⟩ := (hspan _).1 ((Submodule.Quotient.mk_eq_zero _).1 hmax)
    refine ⟨Pi.single maxCircle (0, n), ?_, funext fun C ↦ ?_⟩
    · rw [mem_totalDegree_circleMappingTorus_iff]
      simp
    · cases C
      · rw [differential_circleMappingTorus_minCircle]
        exact Prod.ext (hx.1 one_ne_zero).symm hmin.symm
      · rw [differential_circleMappingTorus_maxCircle, Pi.single_eq_same]
        exact Prod.ext hn (hx.2.2.2 (by norm_num)).symm
  · refine Prod.ext (congrArg Prod.snd (differential_circleMappingTorus_minCircle ε y))
      ((Submodule.Quotient.mk_eq_zero _).2 ((hspan _).2 ⟨(y maxCircle).2, ?_⟩))
    exact (congrArg Prod.fst (differential_circleMappingTorus_maxCircle ε y)).symm

/-- **`H₂` of the model is the `(1 - ε)`-torsion of `R`**: the cycles of total degree `2` are the
edge coefficients `n` of the maximum circle with `(1 - ε) n = 0`, and nothing has total degree
`3`. -/
theorem nonempty_linearEquiv_homology_two_circleMappingTorusComplex :
    Nonempty ((circleMappingTorusComplex R ε).homology 2 ≃ₗ[R]
      LinearMap.ker ((1 - (ε : ℤ)) • LinearMap.id : R →ₗ[R] R)) := by
  refine nonempty_linearEquiv_homology_of_cycles (k := 2) ε
    (LinearMap.snd R R R ∘ₗ LinearMap.proj maxCircle) _ (fun x _ hdx ↦ ?_) (fun n hn ↦ ?_)
    (fun x hx _ hz ↦ ?_) (fun y _ ↦ by simp)
  · -- the vertex coefficient of the Bott differential on the maximum circle vanishes
    have h := congrArg Prod.fst (congrFun hdx maxCircle)
    rw [differential_circleMappingTorus_maxCircle] at h
    exact LinearMap.mem_ker.2 h
  · refine ⟨Pi.single maxCircle (0, n), ?_, funext fun C ↦ ?_, by simp⟩
    · rw [mem_totalDegree_circleMappingTorus_iff]
      simp
    · cases C
      · rw [differential_circleMappingTorus_minCircle, Pi.zero_apply]
      · rw [differential_circleMappingTorus_maxCircle, Pi.single_eq_same]
        exact Prod.ext (LinearMap.mem_ker.1 hn) rfl
  · rw [mem_totalDegree_circleMappingTorus_iff] at hx
    refine ⟨0, zero_mem _, (map_zero _).trans (funext fun C ↦ ?_)⟩
    cases C
    · exact Prod.ext (hx.1 (by simp)).symm (hx.2.1 (by simp)).symm
    · exact Prod.ext (hx.2.2.1 (by simp)).symm (by simpa using hz.symm)

/-- **The other homology groups of the model vanish**: it has no chains outside total degrees
`0`, `1` and `2`. -/
theorem isZero_homology_circleMappingTorusComplex {k : ℤ} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) :
    IsZero ((circleMappingTorusComplex R ε).homology k) := by
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [(circleMappingTorusComplex R ε).exactAt_iff' (k + 1) k (k - 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rintro ⟨x, hx⟩ -
  refine ⟨0, Subtype.ext ?_⟩
  rw [map_zero]
  rw [mem_totalDegree_circleMappingTorus_iff] at hx
  funext C
  cases C
  · exact Prod.ext (hx.1 h0).symm (hx.2.1 h1).symm
  · exact Prod.ext (hx.2.2.1 h1).symm (hx.2.2.2 h2).symm

/-! ### The torus and the Klein bottle -/

/-- **`H₁ = R²` for the torus model**: with trivial coefficients on both critical circles nothing
in total degree `1` bounds. -/
theorem nonempty_linearEquiv_homology_one_circleMappingTorusComplex_one :
    Nonempty ((circleMappingTorusComplex R 1).homology 1 ≃ₗ[R] R × R) :=
  (nonempty_linearEquiv_homology_one_circleMappingTorusComplex 1).map fun e ↦
    e ≪≫ₗ (LinearEquiv.refl R R).prodCongr (Submodule.quotEquivOfEqBot _ (by simp))

/-- **`H₂ = R` for the torus model**, spanned by the edge of the maximum circle. -/
theorem nonempty_linearEquiv_homology_two_circleMappingTorusComplex_one :
    Nonempty ((circleMappingTorusComplex R 1).homology 2 ≃ₗ[R] R) :=
  (nonempty_linearEquiv_homology_two_circleMappingTorusComplex 1).map fun e ↦
    e ≪≫ₗ LinearEquiv.ofTop _ (by simp)

/-- **`H₁ = ℤ × ℤ/2` for the Klein bottle model over `ℤ`**: the vertex of the maximum circle,
whose coefficients form the sign system, has order two in homology. -/
theorem nonempty_linearEquiv_homology_one_circleMappingTorusComplex_neg_one :
    Nonempty ((circleMappingTorusComplex ℤ (-1)).homology 1 ≃ₗ[ℤ] ℤ × ZMod 2) :=
  (nonempty_linearEquiv_homology_one_circleMappingTorusComplex (-1)).map fun e ↦
    e ≪≫ₗ (LinearEquiv.refl ℤ ℤ).prodCongr
      (Submodule.quotEquivOfEq _ _ (by norm_num [Ideal.span]) ≪≫ₗ
        (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv)

/-- **`H₂ = 0` for the Klein bottle model over `ℤ`**: the edge of the maximum circle has
boundary twice its vertex, so no nonzero multiple of it is a cycle. -/
theorem isZero_homology_two_circleMappingTorusComplex_neg_one :
    IsZero ((circleMappingTorusComplex ℤ (-1)).homology 2) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_two_circleMappingTorusComplex (R := ℤ) (-1)
  have hker : LinearMap.ker ((1 - ((-1 : ℤˣ) : ℤ)) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) = ⊥ := by
    ext n
    simp
  rw [hker] at e
  have := e.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- **The Klein bottle model computes the homology of the Klein bottle**: in every degree `k`, the
homology of the cellular Bott model of the height on the Klein bottle over `ℤ` is isomorphic to the
singular homology `H_k(K; ℤ)`. Both are `ℤ`, `ℤ × ℤ/2` and `0` in degrees `0`, `1` and `k ≥ 2`. -/
theorem nonempty_linearEquiv_homology_circleMappingTorusComplex_kleinBottle (k : ℕ) :
    Nonempty ((circleMappingTorusComplex ℤ (-1)).homology k ≃ₗ[ℤ]
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of KleinBottle)) := by
  match k with
  | 0 =>
    rw [Nat.cast_zero]
    exact (nonempty_linearEquiv_homology_zero_circleMappingTorusComplex (-1)).map fun e ↦
      e ≪≫ₗ KleinBottle.singularHomologyZeroLinearEquiv.symm
  | 1 =>
    rw [Nat.cast_one]
    exact nonempty_linearEquiv_homology_one_circleMappingTorusComplex_neg_one.map fun e ↦
      e ≪≫ₗ KleinBottle.singularHomologyOneLinearEquiv.symm
  | k + 2 =>
    have h : IsZero ((circleMappingTorusComplex ℤ (-1)).homology ((k + 2 : ℕ) : ℤ)) := by
      rcases k with _ | k
      · exact isZero_homology_two_circleMappingTorusComplex_neg_one
      · exact isZero_homology_circleMappingTorusComplex (-1) (by omega) (by omega) (by omega)
    exact ⟨(h.iso (KleinBottle.isZero_singularHomology_of_two_le (by omega))).toLinearEquiv⟩

end BottChainData

end TauCeti
