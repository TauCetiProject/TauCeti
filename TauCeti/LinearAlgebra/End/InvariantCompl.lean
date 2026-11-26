/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Kernel and cokernel of an endomorphism on an invariant summand

Let `T` be an endomorphism of a module `M = p ⊕ q` over a ring, where both summands are
`T`-invariant. If `T` is injective on `q`, the kernel of `T` lies in `p`, and the inclusion of `p`
identifies the kernel of the restriction `T|p` with that of `T` (`LinearMap.kerRestrictEquiv`). If
`T` is surjective on `q`, the inclusion of `p` identifies the cokernel of `T|p` with that of `T`
(`LinearMap.cokerRestrictEquiv`). No choice beyond the splitting is involved.

## Main definitions

* `LinearMap.kerRestrictEquiv`, `LinearMap.cokerRestrictEquiv`: the kernel and cokernel of `T` are
  those of its restriction to `p`.
-/

public section

noncomputable section

namespace LinearMap

section Restrict

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {T : M →ₗ[R] M}
  {p q : Submodule R M} (hpq : IsCompl p q) (hp : ∀ x ∈ p, T x ∈ p) (hq : ∀ x ∈ q, T x ∈ q)

include hpq hp hq in
/-- If `x ∈ p` is `T a + T b` with `a ∈ p` and `b ∈ q`, then `x = T a`, since `T b` lies in
`p ⊓ q = ⊥`. -/
private theorem eq_of_add_mem_range {a b : M} (ha : a ∈ p) (hb : b ∈ q) {x : M} (hx : x ∈ p)
    (h : x = T a + T b) : x = T a := by
  have hTb : T b ∈ p ⊓ q := ⟨by simpa [h] using sub_mem hx (hp a ha), hq b hb⟩
  rw [hpq.inf_eq_bot, Submodule.mem_bot] at hTb
  rw [h, hTb, add_zero]

include hpq hp hq in
/-- The kernel of `T` lies in `p` when `T` is injective on `q`. -/
private theorem ker_le (hT : Function.Injective (T.restrict hq)) : ker T ≤ p := by
  intro v hv
  obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hpq.codisjoint v
  have hab : T a + T b = 0 := by simpa using hv
  have hTa : 0 = T a := eq_of_add_mem_range hpq hp hq ha hb (zero_mem p) hab.symm
  have hTb : T b = 0 := by rwa [← hTa, zero_add] at hab
  have hb0 : (⟨b, hb⟩ : q) = 0 := hT (Subtype.ext (by simpa using hTb))
  simpa [show b = 0 from congrArg Subtype.val hb0] using ha

/-- The summand `q` lies in the range of `T` when `T` is surjective on `q`. -/
private theorem le_range (hT : Function.Surjective (T.restrict hq)) : q ≤ range T := fun b hb ↦ by
  obtain ⟨c, hc⟩ := hT ⟨b, hb⟩
  exact ⟨c, congrArg Subtype.val hc⟩

section Ker

variable (hT : Function.Injective (T.restrict hq))

/-- **The kernel of `T` is that of its restriction to `p`**, when `M = p ⊕ q` with both summands
`T`-invariant and `T` injective on `q`; the isomorphism is induced by the inclusion of `p`. -/
def kerRestrictEquiv : ker (T.restrict hp) ≃ₗ[R] ker T :=
  (LinearEquiv.ofEq _ _ (ker_restrict hp)).trans
    (Submodule.comapSubtypeEquivOfLe (ker_le hpq hp hq hT))

/-- `LinearMap.kerRestrictEquiv` is the inclusion of `p`. -/
@[simp]
theorem coe_kerRestrictEquiv_apply (x : ker (T.restrict hp)) :
    (kerRestrictEquiv hpq hp hq hT x : M) = ((x : p) : M) :=
  (rfl)

/-- The inverse of `LinearMap.kerRestrictEquiv` sends a vector of the kernel of `T` to itself, as a
vector of `p`. -/
@[simp]
theorem coe_kerRestrictEquiv_symm_apply (v : ker T) :
    (((kerRestrictEquiv hpq hp hq hT).symm v : p) : M) = v := by
  rw [← coe_kerRestrictEquiv_apply hpq hp hq hT, LinearEquiv.apply_symm_apply]

end Ker

section Coker

variable (hT : Function.Surjective (T.restrict hq))

/-- **The cokernel of `T` is that of its restriction to `p`**, when `M = p ⊕ q` with both summands
`T`-invariant and `T` surjective on `q`; the isomorphism is induced by the inclusion of `p`. -/
def cokerRestrictEquiv : (p ⧸ range (T.restrict hp)) ≃ₗ[R] (M ⧸ range T) :=
  LinearEquiv.ofBijective
    ((range (T.restrict hp)).mapQ (range T) p.subtype fun x ⟨y, hy⟩ ↦
      ⟨y, by simpa using congrArg Subtype.val hy⟩)
    ⟨by
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      obtain ⟨v, hv⟩ := hx
      obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hpq.codisjoint v
      refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
      exact (eq_of_add_mem_range hpq hp hq ha hb x.property (by simpa using hv.symm)).symm, by
      intro y
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
      obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hpq.codisjoint v
      refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
      rw [Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      simpa using neg_mem (le_range hq hT hb)⟩

/-- `LinearMap.cokerRestrictEquiv` sends the class of `x ∈ p` to the class of `x`. -/
@[simp]
theorem cokerRestrictEquiv_mk (x : p) :
    cokerRestrictEquiv hpq hp hq hT (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x : M) :=
  (rfl)

/-- The inverse of `LinearMap.cokerRestrictEquiv` sends the class of `x ∈ p` modulo the range of
`T` to its class modulo the range of the restriction. -/
@[simp]
theorem cokerRestrictEquiv_symm_mk (x : p) :
    (cokerRestrictEquiv hpq hp hq hT).symm (Submodule.Quotient.mk (x : M)) =
      Submodule.Quotient.mk x := by
  rw [LinearEquiv.symm_apply_eq, cokerRestrictEquiv_mk]

end Coker

end Restrict

end LinearMap
