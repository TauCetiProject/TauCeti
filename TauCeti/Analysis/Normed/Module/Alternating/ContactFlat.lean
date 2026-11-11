/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.LinearAlgebra.BilinearForm.Contact
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The contact flat map of a covector and a two-form

For a covector `a` and an alternating two-form `ω` on a normed space `V`, the **contact flat map**
`ContinuousAlternatingMap.contactFlatMap a ω` is `v ↦ ι_v ω + a(v) a`, a continuous linear map from
`V` to its dual. When `a` is a contact covector for `ω`, that is `a ≠ 0` and `ω` is nondegenerate
on `ker a`, the contact flat map is invertible in finite dimensions
(`ContinuousAlternatingMap.isInvertible_contactFlatMap`), and the preimage of `a` is the Reeb
vector: `a(R) = 1` and `ι_R ω = 0`. The contact flat map depends smoothly on `a` and `ω`
(`ContinuousAlternatingMap.contDiffOn_contactFlatMap`), so inverting it produces smooth vector
fields from smooth families of contact data.

This is the pointwise form, on a single normed space and with forms given as continuous
alternating maps, of the contact flat map `TauCeti.SmoothForm.contactFlat` of a one-form on a
manifold. The linear algebra is that of `Module.Dual.IsContact`.

## Main declarations

* `ContinuousAlternatingMap.contactFlatMap`: the contact flat map `v ↦ ι_v ω + a(v) a`.
* `ContinuousAlternatingMap.isInvertible_contactFlatMap`: it is invertible at a contact covector.
* `ContinuousAlternatingMap.reeb_of_contactFlatMap_apply_eq`: the preimage of `a` satisfies the
  Reeb equations.
* `ContinuousAlternatingMap.contactMoser_of_contactFlatMap_apply_eq`: the horizontal contact-Moser
  equations, `a(X) = 0` and `ι_X ω = b(R) a - b`, for the preimage `X` of `b(R) a - b`.
-/

public section

namespace ContinuousAlternatingMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The contact flat map `v ↦ ι_v ω + a(v) a` of a covector `a` and a two-form `ω`, with values
in the dual. -/
noncomputable def contactFlatMap (a : V [⋀^Fin 1]→L[𝕜] 𝕜) (ω : V [⋀^Fin 2]→L[𝕜] 𝕜) :
    V →L[𝕜] V →L[𝕜] 𝕜 :=
  flatL 𝕜 V 𝕜 ω + (toDual a).smulRight (toDual a)

/-- The contact flat map evaluates as `(v, w) ↦ ω(v, w) + a(v) a(w)`. -/
@[simp]
theorem contactFlatMap_apply_apply (a : V [⋀^Fin 1]→L[𝕜] 𝕜) (ω : V [⋀^Fin 2]→L[𝕜] 𝕜)
    (v w : V) : contactFlatMap a ω v w = ω ![v, w] + a ![v] * a ![w] := by
  simp [contactFlatMap]

/-- The pointwise contact condition, `a ≠ 0` with `ω` nondegenerate on `ker a`, as the linear
contact condition `Module.Dual.IsContact`. -/
theorem isContact_toDual {a : V [⋀^Fin 1]→L[𝕜] 𝕜} {ω : V [⋀^Fin 2]→L[𝕜] 𝕜} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) :
    Module.Dual.IsContact (toDual a : V →ₗ[𝕜] 𝕜) (flatL 𝕜 V 𝕜 ω).toLinearMap₁₂ := by
  refine (Module.Dual.isContact_iff_of_isRefl (isAlt_toLinearMap₁₂_flatL ω).isRefl).2
    ⟨fun h0 ↦ hne ?_, fun v hv hvw ↦ hnd v (by simpa using hv) fun w hw ↦ by
      simpa using hvw w (by simpa using hw)⟩
  ext m
  have hm : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [hm, ← toDual_apply]
  exact LinearMap.congr_fun h0 (m 0)

/-- At a contact covector `a` for an alternating form `ω`, the contact flat map is invertible. -/
theorem isInvertible_contactFlatMap [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V]
    {a : V [⋀^Fin 1]→L[𝕜] 𝕜} {ω : V [⋀^Fin 2]→L[𝕜] 𝕜} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) :
    (contactFlatMap a ω).IsInvertible := by
  have hsep := (isContact_toDual hne hnd).separatingLeft_add_smulRight
    (isAlt_toLinearMap₁₂_flatL ω)
  refine ContinuousLinearMap.isInvertible_of_injective <|
    (injective_iff_map_eq_zero _).2 fun v hv ↦ hsep v fun w ↦ ?_
  have h := contactFlatMap_apply_apply a ω v w
  rw [hv] at h
  simpa using h.symm

/-- The vector `R` with `ι_R ω + a(R) a = a` satisfies the Reeb equations `a(R) = 1`,
`ι_R ω = 0`, as soon as `a(R) ≠ 0`. -/
theorem reeb_of_contactFlatMap_apply_eq {a : V [⋀^Fin 1]→L[𝕜] 𝕜}
    {ω : V [⋀^Fin 2]→L[𝕜] 𝕜} {R : V} (hR : contactFlatMap a ω R = toDual a) (h0 : a ![R] ≠ 0) :
    a ![R] = 1 ∧ ∀ w, ω ![R, w] = 0 := by
  have hR' (w : V) : ω ![R, w] + a ![R] * a ![w] = a ![w] := by
    rw [← contactFlatMap_apply_apply, hR, toDual_apply]
  have h1 : a ![R] = 1 := by
    have := hR' R
    rw [ω.map_eq_zero_of_eq ![R, R] (i := 0) (j := 1) rfl Fin.zero_ne_one, zero_add] at this
    exact (mul_eq_left₀ h0).1 this
  exact ⟨h1, fun w ↦ by simpa [h1] using hR' w⟩

/-- **The contact Moser equation, pointwise.** Let `A` be the contact flat map of `a` and `ω`,
let `R` solve `A R = a` with `a(R) ≠ 0`, and let `X` solve `A X = b(R) a - b`. Then `X` lies in
`ker a` and `ι_X ω = b(R) a - b`. -/
theorem contactMoser_of_contactFlatMap_apply_eq {a b : V [⋀^Fin 1]→L[𝕜] 𝕜}
    {ω : V [⋀^Fin 2]→L[𝕜] 𝕜} {R X : V} (hR : contactFlatMap a ω R = toDual a) (h0 : a ![R] ≠ 0)
    (hX : contactFlatMap a ω X = toDual b R • toDual a - toDual b) :
    a ![X] = 0 ∧ ω.curryLeft X = b ![R] • a - b := by
  obtain ⟨h1, hRω⟩ := reeb_of_contactFlatMap_apply_eq hR h0
  have hX' (w : V) : ω ![X, w] + a ![X] * a ![w] = b ![R] * a ![w] - b ![w] := by
    rw [← contactFlatMap_apply_apply, hX]
    simp [toDual_apply]
  have hXa : a ![X] = 0 := by
    have := hX' R
    have hswap : ω ![X, R] = -ω ![R, X] := by
      simpa using ω.map_swap ![R, X] (i := 0) (j := 1) Fin.zero_ne_one
    rw [hswap, hRω, neg_zero, zero_add, h1, mul_one, mul_one, sub_self] at this
    exact this
  refine ⟨hXa, ?_⟩
  ext m
  have hm : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [curryLeft_apply_apply, hm]
  simpa [hXa] using hX' (m 0)

/-- At a contact covector `a` for `ω`, the vector `R` solving `ι_R ω + a(R) a = a` is the Reeb
vector, so `a(R) = 1 ≠ 0`. -/
theorem apply_ne_zero_of_contactFlatMap_apply_eq {a : V [⋀^Fin 1]→L[𝕜] 𝕜}
    {ω : V [⋀^Fin 2]→L[𝕜] 𝕜} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) {R : V}
    (hR : contactFlatMap a ω R = toDual a) : a ![R] ≠ 0 := by
  have h := ((isContact_toDual hne hnd).add_smulRight_apply_eq_self_iff
    (isAlt_toLinearMap₁₂_flatL ω) (r := R)).1 <| LinearMap.ext fun w ↦ by
      simpa using (congrArg (fun f : V →L[𝕜] 𝕜 ↦ f w) hR)
  rw [← toDual_apply]
  exact h.1 ▸ one_ne_zero

/-- The contact flat map depends smoothly on the covector and the two-form. -/
theorem contDiffOn_contactFlatMap {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {n : WithTop ℕ∞} {s : Set E} {a : E → V [⋀^Fin 1]→L[𝕜] 𝕜} {ω : E → V [⋀^Fin 2]→L[𝕜] 𝕜}
    (ha : ContDiffOn 𝕜 n a s) (hω : ContDiffOn 𝕜 n ω s) :
    ContDiffOn 𝕜 n (fun p ↦ contactFlatMap (a p) (ω p)) s := by
  have hd := ha.continuousLinearMap_comp (toDual : (V [⋀^Fin 1]→L[𝕜] 𝕜) →L[𝕜] V →L[𝕜] 𝕜)
  exact (hω.continuousLinearMap_comp (flatL 𝕜 V 𝕜)).add (hd.smulRight hd)

end ContinuousAlternatingMap
