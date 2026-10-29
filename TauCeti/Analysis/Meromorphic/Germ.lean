/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Order.Filter.Germ.Basic

/-!
# The field of meromorphic germs at a point

Let `𝕜` be a nontrivially normed field and `a : 𝕜`. A function meromorphic at `a` is only
determined, as such, on a punctured neighbourhood of `a`: Mathlib's `MeromorphicAt` ignores the
value at `a` itself. This file collects the germs along the punctured neighbourhood filter
`𝓝[≠] a` of the functions `𝕜 → 𝕜` which are meromorphic at `a` into a subring
`TauCeti.meromorphicGerms 𝕜 a` of Mathlib's ring of germs `Filter.Germ (𝓝[≠] a) 𝕜`, and shows
that it is a field.

The inverse of a germ is the pointwise inverse. It is a multiplicative inverse because, by the
principle of isolated zeros (`MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`), a
meromorphic function whose punctured germ is nonzero vanishes at no point of some punctured
neighbourhood (`MeromorphicAt.germ_ne_zero_iff`).

For `𝕜 = ℂ` this is the local field of meromorphic functions in one variable; it is identified
with the fraction field of the ring of holomorphic germs at `a` in
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.MeromorphicGerm`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
-/

public noncomputable section

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a : 𝕜}

/-- A function meromorphic at `a` has a nonzero germ on the punctured neighbourhoods of `a`
exactly when it vanishes at no point of some punctured neighbourhood of `a`. -/
theorem MeromorphicAt.germ_ne_zero_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} (hf : MeromorphicAt f a) :
    (f : Germ (𝓝[≠] a) E) ≠ 0 ↔ ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
  rw [Ne, ← Germ.coe_zero, Germ.coe_eq]
  refine ⟨fun h ↦ hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left h, fun h h0 ↦ ?_⟩
  exact (h.and h0).exists.elim fun z hz ↦ hz.1 hz.2

namespace TauCeti

variable (𝕜) in
/-- The germs on the punctured neighbourhoods of `a` of the functions meromorphic at `a`. -/
def meromorphicGerms (a : 𝕜) : Subring (Germ (𝓝[≠] a) 𝕜) where
  carrier := {φ | ∃ f : 𝕜 → 𝕜, MeromorphicAt f a ∧ (f : Germ (𝓝[≠] a) 𝕜) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨1, MeromorphicAt.const 1 a, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨0, MeromorphicAt.const 0 a, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- A punctured germ is meromorphic at `a` when it is the germ of a function meromorphic at
`a`. -/
theorem mem_meromorphicGerms_iff {φ : Germ (𝓝[≠] a) 𝕜} :
    φ ∈ meromorphicGerms 𝕜 a ↔ ∃ f : 𝕜 → 𝕜, MeromorphicAt f a ∧ (f : Germ (𝓝[≠] a) 𝕜) = φ :=
  Iff.rfl

/-- The germ of a function lies in `meromorphicGerms 𝕜 a` exactly when the function is
meromorphic at `a`. -/
@[simp]
theorem coe_mem_meromorphicGerms {f : 𝕜 → 𝕜} :
    (f : Germ (𝓝[≠] a) 𝕜) ∈ meromorphicGerms 𝕜 a ↔ MeromorphicAt f a :=
  ⟨fun ⟨_, hg, hgf⟩ ↦ hg.congr (Germ.coe_eq.1 hgf), fun hf ↦ ⟨f, hf, rfl⟩⟩

namespace meromorphicGerms

/-- The inverse of a meromorphic germ is its pointwise inverse. -/
instance : Inv (meromorphicGerms 𝕜 a) where
  inv φ := ⟨(φ : Germ (𝓝[≠] a) 𝕜)⁻¹, by
    obtain ⟨f, hf, hφ⟩ := φ.2
    rw [← hφ, ← Germ.coe_inv, coe_mem_meromorphicGerms]
    exact hf.inv⟩

@[simp, norm_cast]
theorem coe_inv (φ : meromorphicGerms 𝕜 a) :
    ((φ⁻¹ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = (φ : Germ (𝓝[≠] a) 𝕜)⁻¹ :=
  rfl

/-- The germs of functions meromorphic at `a`, on punctured neighbourhoods of `a`, form a
field. -/
instance instField : Field (meromorphicGerms 𝕜 a) where
  exists_pair_ne := ⟨0, 1, fun h ↦ zero_ne_one (congrArg Subtype.val h)⟩
  mul_inv_cancel φ hφ := by
    obtain ⟨f, hf, hφf⟩ := φ.2
    have hne : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
      rw [← hf.germ_ne_zero_iff, hφf]
      exact fun h ↦ hφ (Subtype.ext h)
    apply Subtype.ext
    rw [Subring.coe_mul, coe_inv, ← hφf, ← Germ.coe_inv, ← Germ.coe_mul, Subring.coe_one,
      ← Germ.coe_one, Germ.coe_eq]
    filter_upwards [hne] with z hz
    exact mul_inv_cancel₀ hz
  inv_zero := Subtype.ext <| by
    rw [coe_inv, ZeroMemClass.coe_zero, ← Germ.coe_zero, ← Germ.coe_inv]
    exact Germ.coe_eq.2 (.of_forall fun _ ↦ inv_zero)
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl

@[simp, norm_cast]
theorem coe_div (φ ψ : meromorphicGerms 𝕜 a) :
    ((φ / ψ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (φ : Germ (𝓝[≠] a) 𝕜) / (ψ : Germ (𝓝[≠] a) 𝕜) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Subring.coe_mul, coe_inv]

@[simp, norm_cast]
theorem coe_zpow (φ : meromorphicGerms 𝕜 a) (n : ℤ) :
    ((φ ^ n : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = (φ : Germ (𝓝[≠] a) 𝕜) ^ n := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, SubmonoidClass.coe_pow]
  | negSucc n => rw [zpow_negSucc, zpow_negSucc, coe_inv, SubmonoidClass.coe_pow]

end meromorphicGerms

end TauCeti
