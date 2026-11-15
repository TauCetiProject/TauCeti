/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import TauCeti.Topology.ContinuousMap.Ordered

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Convex.AffineOn

/-!
# Choquet–Rudin barycenters in locally convex spaces

Let `K` be a compact convex subset of a real Hausdorff locally convex topological vector space `E`,
and let `φ` be a positive real linear functional on `C(K, ℝ)` normalized by `φ 1 = 1` (in particular
forcing `K` to be nonempty). There is a unique point `b ∈ K`, the *barycenter* (or *resultant*)
`TauCeti.barycenter K φ`, such that

```text
ℓ b = φ (ℓ|_K)   for every ℓ : StrongDual ℝ E.
```

Uniqueness requires only `SeparatingDual ℝ E`. Existence reduces by compactness of `K` to finite
collections `s : Finset (StrongDual ℝ E)` of functionals: the joint evaluation `L : E →L[ℝ] (s → ℝ)`
maps `K` to a compact convex subset of `s → ℝ`, and separating `(φ (ℓ|_K))_{ℓ ∈ s}` from `L '' K`
by `geometric_hahn_banach_closed_point` would produce a functional exceeding on `φ` its pointwise
upper bound on `K`.

Every continuous convex function on `K` is the pointwise supremum of continuous affine minorants
(`ConvexOn.exists_affine_le_of_lt`), from which the Choquet–Jensen inequality `f b ≤ φ f` follows.
Applying Jensen's inequality to both `±(ℓ' ∘ T)` shows that continuous maps out of `K` preserving
binary convex combinations intertwine `TauCeti.barycenter` with pushforward of functionals. On a
compact set `K`, pointwise convergence of normalized positive functionals on `StrongDual ℝ E`
implies convergence of their barycenters in `E`.

## Main definitions

* `TauCeti.barycenter K φ`: the Choquet–Rudin barycenter in `K` of a functional `φ` on `C(K, ℝ)`,
  equal to `0` when no representing point in `K` exists.

## Main results

* `TauCeti.existsUnique_mem_forall_strongDual_eq`: existence and uniqueness of the barycenter.
* `TauCeti.barycenter_mem`, `TauCeti.strongDual_barycenter`, `TauCeti.barycenter_eq_iff`:
  membership and dual characterization of `barycenter K φ`.
* `TauCeti.barycenter_evalAlgHom`, `TauCeti.barycenter_evalPositiveLinearMap`,
  `TauCeti.barycenter_evalCLM`: the barycenter of point evaluation at `x : K` is `x`.
* `TauCeti.apply_barycenter_le`, `TauCeti.apply_barycenter_le_of_convexOn`: the Choquet–Jensen
  inequality for continuous convex functions on `K`.
* `TauCeti.strongDual_map_barycenter`, `TauCeti.map_barycenter`, `TauCeti.affineMap_barycenter`:
  covariance of `barycenter` under continuous maps preserving convex combinations and continuous
  affine maps.
* `TauCeti.tendsto_barycenter`: convergence of barycenters from dual-wise convergence of
  functionals.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Theorem 3.27.
* R. R. Phelps, *Lectures on Choquet's Theorem*, 2nd ed., Propositions 1.1 and 1.2.
-/

public section

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace TauCeti

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The Choquet–Rudin barycenter (resultant) of a functional `φ` on `C(K, ℝ)` in `K`: the point
`b ∈ K` satisfying `ℓ b = φ (ℓ|_K)` for every continuous linear functional `ℓ : StrongDual ℝ E`
when such a point exists (in particular, whenever `K` is compact and convex in a Hausdorff locally
convex real space and `φ` is a positive linear functional with `φ 1 = 1`), and `0` otherwise. -/
def barycenter (K : Set E) {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ] (φ : Φ) : E :=
  open Classical in
  if h : ∃ b ∈ K, ∀ ℓ : StrongDual ℝ E, ℓ b = φ ((ℓ : C(E, ℝ)).restrict K) then h.choose else 0

/-- Functional extensionality for `barycenter`: two functionals agreeing on `C(K, ℝ)` have the same
barycenter. -/
theorem barycenter_congr {K : Set E} {Φ Ψ : Type*} [FunLike Φ C(K, ℝ) ℝ] [FunLike Ψ C(K, ℝ) ℝ]
    {φ : Φ} {ψ : Ψ} (h : ∀ f, φ f = ψ f) : barycenter K φ = barycenter K ψ := by
  have hp : (fun b => b ∈ K ∧ ∀ ℓ : StrongDual ℝ E, ℓ b = φ ((ℓ : C(E, ℝ)).restrict K)) =
      (fun b => b ∈ K ∧ ∀ ℓ : StrongDual ℝ E, ℓ b = ψ ((ℓ : C(E, ℝ)).restrict K)) :=
    funext fun _ => propext (by simp [h])
  exact congrArg
    (fun P : E → Prop => open Classical in if hP : ∃ b, P b then hP.choose else 0) hp

end Defs

section SeparatingDual

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [SeparatingDual ℝ E]

/-- In a space with separating continuous dual, a point `x ∈ K` satisfying `ℓ x = φ (ℓ|_K)` for all
`ℓ : StrongDual ℝ E` is `barycenter K φ`. -/
theorem barycenter_eq_of_mem {K : Set E} {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ] {φ : Φ} {x : E}
    (hxK : x ∈ K) (hx : ∀ ℓ : StrongDual ℝ E, ℓ x = φ ((ℓ : C(E, ℝ)).restrict K)) :
    barycenter K φ = x := by
  have hex : ∃ b ∈ K, ∀ ℓ : StrongDual ℝ E, ℓ b = φ ((ℓ : C(E, ℝ)).restrict K) := ⟨x, hxK, hx⟩
  simp only [barycenter, hex, ↓reduceDIte]
  exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ =>
    (hex.choose_spec.2 ℓ).trans (hx ℓ).symm

/-- The barycenter of point evaluation (as an algebra homomorphism) at `x : K` is `x`. -/
@[simp]
theorem barycenter_evalAlgHom (K : Set E) (x : K) :
    barycenter K (ContinuousMap.evalAlgHom ℝ ℝ x) = x :=
  barycenter_eq_of_mem x.2 fun _ => rfl

/-- The barycenter of point evaluation (as a positive linear map) at `x : K` is `x`. -/
@[simp]
theorem barycenter_evalPositiveLinearMap (K : Set E) (x : K) :
    barycenter K (ContinuousMap.evalPositiveLinearMap ℝ ℝ x) = x :=
  barycenter_eq_of_mem x.2 fun _ => by simp

/-- The barycenter of point evaluation (as a continuous linear map) at `x : K` is `x`. -/
@[simp]
theorem barycenter_evalCLM (K : Set E) (x : K) :
    barycenter K (ContinuousMap.evalCLM ℝ (M := ℝ) x) = x :=
  barycenter_eq_of_mem x.2 fun _ => rfl

end SeparatingDual

section LocallyConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- **Existence and uniqueness of the Choquet–Rudin barycenter.** If `K` is a compact convex subset
of a Hausdorff locally convex real space `E` and `φ` is a positive linear functional on `C(K, ℝ)`
with `φ 1 = 1`, there is a unique `b ∈ K` such that `ℓ b = φ (ℓ|_K)` for every
`ℓ : StrongDual ℝ E`. -/
theorem existsUnique_mem_forall_strongDual_eq {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K)
    {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ]
    (φ : Φ) (hφ₁ : φ 1 = 1) :
    ∃! b, b ∈ K ∧ ∀ ℓ : StrongDual ℝ E, ℓ b = φ ((ℓ : C(E, ℝ)).restrict K) := by
  classical
  -- Compactness reduces the intersection of all dual hyperplanes with `K` to finite subsets `s`.
  suffices hex : ∃ b ∈ K, ∀ ℓ : StrongDual ℝ E, ℓ b = φ ((ℓ : C(E, ℝ)).restrict K) by
    obtain ⟨b, hbK, hb⟩ := hex
    exact ⟨b, ⟨hbK, hb⟩, fun y ⟨_, hy⟩ =>
      (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => (hy ℓ).trans (hb ℓ).symm⟩
  obtain ⟨b, hbK, hb⟩ := hK.inter_iInter_nonempty
    (fun ℓ : StrongDual ℝ E => {x : E | ℓ x = φ ((ℓ : C(E, ℝ)).restrict K)})
    (fun ℓ => isClosed_eq ℓ.continuous continuous_const) fun s => by
      -- Map `K` to `s → ℝ` by evaluating the finitely many functionals in `s`.
      let L : E →L[ℝ] (s → ℝ) := ContinuousLinearMap.pi fun i : s => (i : StrongDual ℝ E)
      let v : s → ℝ := fun i => φ (((i : StrongDual ℝ E) : C(E, ℝ)).restrict K)
      suffices hv : v ∈ L '' K by
        obtain ⟨x, hxK, hLx⟩ := hv
        exact ⟨x, hxK, mem_iInter₂.2 fun ℓ hℓ => congr_fun hLx ⟨ℓ, hℓ⟩⟩
      by_contra hv
      obtain ⟨ψ, u, hψK, hψv⟩ := geometric_hahn_banach_closed_point
        (hKc.linear_image L.toLinearMap) (hK.image L.continuous).isClosed hv
      have hψ_eq (w : s → ℝ) : ψ w = ∑ i : s, w i * ψ (Pi.single i 1) := by
        have hw : w = ∑ i : s, w i • Pi.single i (1 : ℝ) := by
          ext j
          simp [Pi.single_apply]
        conv_lhs => rw [hw]
        simp [map_sum]
      let ℓ₀ : StrongDual ℝ E := ∑ i : s, ψ (Pi.single i 1) • (i : StrongDual ℝ E)
      have hℓ₀_le (x : K) : ((ℓ₀ : C(E, ℝ)).restrict K) x ≤ u := by
        have hx : ℓ₀ x = ψ (L x) := by
          rw [hψ_eq]
          simp [ℓ₀, L, mul_comm]
        exact (hx.trans_lt (hψK (L x) (mem_image_of_mem L x.2))).le
      have hφ_le : φ ((ℓ₀ : C(E, ℝ)).restrict K) ≤ u := by
        simpa [hφ₁] using ContinuousMap.apply_le_smul_map_one_of_forall_le φ hℓ₀_le
      have hℓ₀_res : (ℓ₀ : C(E, ℝ)).restrict K =
          ∑ i : s, ψ (Pi.single i 1) • (((i : StrongDual ℝ E) : C(E, ℝ)).restrict K) := by
        ext x
        simp [ℓ₀]
      have hφ_eq : φ ((ℓ₀ : C(E, ℝ)).restrict K) = ψ v := by
        rw [hℓ₀_res, map_sum, hψ_eq]
        exact Finset.sum_congr rfl fun i _ => by simp [v, mul_comm]
      linarith
  exact ⟨b, hbK, fun ℓ => mem_iInter.1 hb ℓ⟩

/-- The Choquet–Rudin barycenter of a normalized positive linear functional on `C(K, ℝ)` lies in
`K`. -/
theorem barycenter_mem {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {Φ : Type*}
    [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ)
    (hφ₁ : φ 1 = 1) : barycenter K φ ∈ K := by
  have hex := (existsUnique_mem_forall_strongDual_eq hK hKc φ hφ₁).exists
  simp only [barycenter, hex, ↓reduceDIte]
  exact hex.choose_spec.1

/-- Every continuous linear functional `ℓ : StrongDual ℝ E` evaluates at `barycenter K φ` to
`φ (ℓ|_K)`. -/
theorem strongDual_barycenter {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {Φ : Type*}
    [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ)
    (hφ₁ : φ 1 = 1) (ℓ : StrongDual ℝ E) :
    ℓ (barycenter K φ) = φ ((ℓ : C(E, ℝ)).restrict K) := by
  have hex := (existsUnique_mem_forall_strongDual_eq hK hKc φ hφ₁).exists
  simp only [barycenter, hex, ↓reduceDIte]
  exact hex.choose_spec.2 ℓ

/-- Dual characterization of `barycenter K φ`: it equals `x` if and only if every continuous linear
functional `ℓ : StrongDual ℝ E` takes the value `φ (ℓ|_K)` at `x`. -/
theorem barycenter_eq_iff {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {Φ : Type*}
    [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ)
    (hφ₁ : φ 1 = 1) {x : E} :
    barycenter K φ = x ↔ ∀ ℓ : StrongDual ℝ E, ℓ x = φ ((ℓ : C(E, ℝ)).restrict K) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  exact forall_congr' fun ℓ => by rw [strongDual_barycenter hK hKc φ hφ₁ ℓ, eq_comm]

/-! ### Choquet–Jensen inequality and affine covariance -/

/-- **Choquet–Jensen inequality** for continuous functions on `K` that are convex with respect to
binary convex combinations in `K`. -/
theorem apply_barycenter_le {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {Φ : Type*}
    [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ)
    (hφ₁ : φ 1 = 1) {f : C(K, ℝ)}
    (hf : ∀ (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      f ⟨a • (x : E) + b • (y : E), hKc x.2 y.2 ha hb hab⟩ ≤ a * f x + b * f y) :
    f ⟨barycenter K φ, barycenter_mem hK hKc φ hφ₁⟩ ≤ φ f := by
  classical
  -- Extend `f` outside `K` by `0` to apply `ConvexOn.exists_affine_le_of_lt` on the closed set `K`.
  have hb : barycenter K φ ∈ K := barycenter_mem hK hKc φ hφ₁
  let g : E → ℝ := fun x => if hx : x ∈ K then f ⟨x, hx⟩ else 0
  have hg_dom : K.domRestrict g = f := funext fun x => dite_eq_left_of_eq_true (eq_true x.2)
  have hgc : ContinuousOn g K :=
    continuousOn_iff_continuous_domRestrict.2 (hg_dom ▸ f.continuous)
  have hg_cvx : ConvexOn ℝ K g := ⟨hKc, fun x hx y hy a b ha hb hab => by
    simp only [g, hx, hy, hKc hx hy ha hb hab, ↓reduceDIte, smul_eq_mul]
    exact hf ⟨x, hx⟩ ⟨y, hy⟩ a b ha hb hab⟩
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  have hrb : r < g (barycenter K φ) := by simpa only [g, hb, ↓reduceDIte] using hr
  obtain ⟨ℓ, c, hle, heq⟩ :=
    hg_cvx.exists_affine_le_of_lt (𝕜 := ℝ) hb hrb hK.isClosed hgc.lowerSemicontinuousOn
  have hminor : (ℓ : C(E, ℝ)).restrict K + ContinuousMap.const K c ≤ f := fun x => by
    simpa [g, x.2] using hle x
  have hφ_minor := OrderHomClass.mono φ hminor
  rw [map_add, ContinuousMap.map_const_eq_smul_map_one, hφ₁, smul_eq_mul, mul_one,
    ← strongDual_barycenter hK hKc φ hφ₁ ℓ] at hφ_minor
  have heq' : ℓ (barycenter K φ) + c = r := by simpa using heq
  exact heq' ▸ hφ_minor

/-- **Choquet–Jensen inequality** for continuous functions on `K` that are concave with respect to
binary convex combinations in `K`. -/
theorem le_apply_barycenter {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {Φ : Type*}
    [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ)
    (hφ₁ : φ 1 = 1) {f : C(K, ℝ)}
    (hf : ∀ (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      a * f x + b * f y ≤ f ⟨a • (x : E) + b • (y : E), hKc x.2 y.2 ha hb hab⟩) :
    φ f ≤ f ⟨barycenter K φ, barycenter_mem hK hKc φ hφ₁⟩ := by
  have hneg := apply_barycenter_le hK hKc φ hφ₁ (f := -f)
    fun x y a b ha hb hab => by
      simp only [ContinuousMap.neg_apply, mul_neg, ← neg_add, neg_le_neg_iff]
      exact hf x y a b ha hb hab
  simpa using hneg

/-- A continuous real function on `K` preserving binary convex combinations takes the value `φ f`
at `barycenter K φ`. -/
theorem apply_barycenter_of_convex_comb {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K)
    {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ]
    (φ : Φ) (hφ₁ : φ 1 = 1) {f : C(K, ℝ)}
    (hf : ∀ (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      f ⟨a • (x : E) + b • (y : E), hKc x.2 y.2 ha hb hab⟩ = a * f x + b * f y) :
    f ⟨barycenter K φ, barycenter_mem hK hKc φ hφ₁⟩ = φ f :=
  le_antisymm
    (apply_barycenter_le hK hKc φ hφ₁ fun x y a b ha hb hab => (hf x y a b ha hb hab).le)
    (le_apply_barycenter hK hKc φ hφ₁ fun x y a b ha hb hab => (hf x y a b ha hb hab).ge)

/-- **Choquet–Jensen inequality** for a function `g : E → ℝ` that is convex and continuous on `K`.
-/
theorem apply_barycenter_le_of_convexOn {K : Set E} (hK : IsCompact K) {g : E → ℝ}
    (hg : ConvexOn ℝ K g) (hgc : ContinuousOn g K) {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ]
    [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ) (hφ₁ : φ 1 = 1) :
    g (barycenter K φ) ≤ φ ⟨K.domRestrict g, hgc.domRestrict⟩ :=
  apply_barycenter_le hK hg.1 φ hφ₁ (f := ⟨K.domRestrict g, hgc.domRestrict⟩)
    fun x y a b ha hb hab => by simpa [smul_eq_mul] using hg.2 x.2 y.2 ha hb hab

/-- **Choquet–Jensen inequality** for a function `g : E → ℝ` that is concave and continuous on `K`.
-/
theorem le_apply_barycenter_of_concaveOn {K : Set E} (hK : IsCompact K) {g : E → ℝ}
    (hg : ConcaveOn ℝ K g) (hgc : ContinuousOn g K) {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ]
    [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ) (hφ₁ : φ 1 = 1) :
    φ ⟨K.domRestrict g, hgc.domRestrict⟩ ≤ g (barycenter K φ) :=
  le_apply_barycenter hK hg.1 φ hφ₁ (f := ⟨K.domRestrict g, hgc.domRestrict⟩)
    fun x y a b ha hb hab => by simpa [smul_eq_mul] using hg.2 x.2 y.2 ha hb hab

/-- A function `g : E → ℝ` that is both convex and concave and continuous on `K` evaluates at
`barycenter K φ` to `φ (g|_K)`. -/
theorem apply_barycenter_of_convexOn_and_concaveOn {K : Set E} (hK : IsCompact K) {g : E → ℝ}
    (hg : ConvexOn ℝ K g) (hgc' : ConcaveOn ℝ K g) (hgc : ContinuousOn g K) {Φ : Type*}
    [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ)
    (hφ₁ : φ 1 = 1) :
    g (barycenter K φ) = φ ⟨K.domRestrict g, hgc.domRestrict⟩ := by
  have hcomb := (hg.1.convexOn_and_concaveOn_iff (f := g)).1 ⟨hg, hgc'⟩
  exact apply_barycenter_of_convex_comb hK hg.1 φ hφ₁ (f := ⟨K.domRestrict g, hgc.domRestrict⟩)
    fun x y a b ha hb hab => by simpa [smul_eq_mul] using hcomb x x.2 y y.2 a b ha hb hab

/-- If `T : C(K, F)` preserves binary convex combinations, every continuous linear functional
`ℓ : StrongDual ℝ F` evaluates at `T (barycenter K φ)` to `φ (ℓ ∘ T)`. -/
theorem strongDual_map_barycenter {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ]
    [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ] (φ : Φ) (hφ₁ : φ 1 = 1)
    {T : C(K, F)}
    (hT : ∀ (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      T ⟨a • (x : E) + b • (y : E), hKc x.2 y.2 ha hb hab⟩ = a • T x + b • T y)
    (ℓ : StrongDual ℝ F) :
    ℓ (T ⟨barycenter K φ, barycenter_mem hK hKc φ hφ₁⟩) = φ ((ℓ : C(F, ℝ)).comp T) :=
  apply_barycenter_of_convex_comb hK hKc φ hφ₁ (f := (ℓ : C(F, ℝ)).comp T)
    fun x y a b ha hb hab => by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass]
      rw [hT x y a b ha hb hab, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **Affine covariance of `barycenter`.** If `T : C(K, L)` preserves binary convex combinations in
a target space `F` with separating continuous dual, then `T` maps `barycenter K φ` to the
barycenter in `L` of the pushforward functional `f ↦ φ (f ∘ T)`. -/
theorem map_barycenter {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [SeparatingDual ℝ F] {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {L : Set F}
    {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ]
    (φ : Φ) (hφ₁ : φ 1 = 1) {T : C(K, L)}
    (hT : ∀ (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      (T ⟨a • (x : E) + b • (y : E), hKc x.2 y.2 ha hb hab⟩ : F) = a • (T x : F) + b • (T y : F)) :
    (T ⟨barycenter K φ, barycenter_mem hK hKc φ hφ₁⟩ : F) =
      barycenter L ((PositiveLinearMap.ofClass φ).comp
        (ContinuousMap.compPositiveLinearMap ℝ ℝ T)) := by
  let bK : K := ⟨barycenter K φ, barycenter_mem hK hKc φ hφ₁⟩
  let Tf : C(K, F) := ⟨fun x => (T x : F), continuous_subtype_val.comp T.continuous⟩
  symm
  refine barycenter_eq_of_mem (T bK).2 fun ℓ => ?_
  have hcomp : ((ℓ : C(F, ℝ)).restrict L).comp T = (ℓ : C(F, ℝ)).comp Tf := rfl
  simpa [PositiveLinearMap.ofClass, hcomp, Tf] using
    strongDual_map_barycenter hK hKc φ hφ₁ (T := Tf) hT ℓ

/-- **Affine-map covariance of `barycenter`.** If `A : E →ᵃ[ℝ] F` is continuous on `K` and maps `K`
into `L`, then `A (barycenter K φ)` is the barycenter in `L` of the pushforward functional. -/
theorem affineMap_barycenter {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [SeparatingDual ℝ F] {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {L : Set F}
    {Φ : Type*} [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ] [OrderHomClass Φ C(K, ℝ) ℝ]
    (φ : Φ) (hφ₁ : φ 1 = 1) (A : E →ᵃ[ℝ] F) (hAc : ContinuousOn A K) (hAL : MapsTo A K L) :
    A (barycenter K φ) =
      barycenter L ((PositiveLinearMap.ofClass φ).comp
        (ContinuousMap.compPositiveLinearMap ℝ ℝ
          ⟨hAL.restrict A K L, hAc.mapsToRestrict hAL⟩)) := by
  have hcomb (x y : K) (a b : ℝ) (_ : 0 ≤ a) (_ : 0 ≤ b) (hab : a + b = 1) :
      A (a • (x : E) + b • (y : E)) = a • A x + b • A y := by
    have ha' : a = 1 - b := eq_sub_of_add_eq hab
    rw [ha', ← AffineMap.lineMap_apply_module, A.apply_lineMap, AffineMap.lineMap_apply_module]
  exact map_barycenter hK hKc φ hφ₁
    (T := ⟨hAL.restrict A K L, hAc.mapsToRestrict hAL⟩)
    fun x y a b ha hb hab => hcomb x y a b ha hb hab

/-- **Convergence of barycenters.** On a compact convex set `K`, if normalized positive functionals
`φs i` converge to `φ` on the restriction to `K` of every continuous linear functional
`ℓ : StrongDual ℝ E`, then `barycenter K (φs i)` converges to `barycenter K φ` in `E`. -/
theorem tendsto_barycenter {ι : Type*} {l : Filter ι} {K : Set E} (hK : IsCompact K)
    (hKc : Convex ℝ K) {Φ Ψ : Type*} [FunLike Φ C(K, ℝ) ℝ] [LinearMapClass Φ ℝ C(K, ℝ) ℝ]
    [OrderHomClass Φ C(K, ℝ) ℝ] [FunLike Ψ C(K, ℝ) ℝ] [LinearMapClass Ψ ℝ C(K, ℝ) ℝ]
    [OrderHomClass Ψ C(K, ℝ) ℝ] {φs : ι → Φ} {φ : Ψ} (hφs : ∀ᶠ i in l, φs i 1 = 1)
    (hφ₁ : φ 1 = 1)
    (hlim : ∀ ℓ : StrongDual ℝ E,
      Tendsto (fun i => φs i ((ℓ : C(E, ℝ)).restrict K)) l (𝓝 (φ ((ℓ : C(E, ℝ)).restrict K)))) :
    Tendsto (fun i => barycenter K (φs i)) l (𝓝 (barycenter K φ)) := by
  refine hK.tendsto_nhds_of_unique_mapClusterPt
    (hφs.mono fun i hi => barycenter_mem hK hKc (φs i) hi) fun c _ hc => ?_
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  have hℓc : MapClusterPt (ℓ c) l (fun i => ℓ (barycenter K (φs i))) :=
    MapClusterPt.continuousAt_comp ℓ.continuous.continuousAt hc
  have hℓlim : Tendsto (fun i => ℓ (barycenter K (φs i))) l (𝓝 (ℓ (barycenter K φ))) := by
    rw [strongDual_barycenter hK hKc φ hφ₁ ℓ]
    exact (hlim ℓ).congr' (hφs.mono fun i hi => (strongDual_barycenter hK hKc (φs i) hi ℓ).symm)
  exact eq_of_nhds_neBot (ClusterPt.mono hℓc hℓlim).neBot

end LocallyConvex

end TauCeti
