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
that it is a field. Constant functions give its natural algebra structure over `𝕜`.

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

/-- The punctured germ of a function meromorphic at the centre. -/
def mk (f : 𝕜 → 𝕜) (hf : MeromorphicAt f a) : meromorphicGerms 𝕜 a :=
  ⟨(f : Germ (𝓝[≠] a) 𝕜), coe_mem_meromorphicGerms.mpr hf⟩

@[simp]
theorem coe_mk (f : 𝕜 → 𝕜) (hf : MeromorphicAt f a) :
    ((mk f hf : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = f := (rfl)

/-- Two meromorphic representatives define the same germ exactly when they agree near the
centre on punctured neighbourhoods. -/
@[simp]
theorem mk_eq_mk_iff {f g : 𝕜 → 𝕜} {hf : MeromorphicAt f a} {hg : MeromorphicAt g a} :
    mk f hf = mk g hg ↔ f =ᶠ[𝓝[≠] a] g :=
  Subtype.ext_iff.trans Germ.coe_eq

/-- Every meromorphic germ has a meromorphic function representative. -/
theorem exists_mk (φ : meromorphicGerms 𝕜 a) :
    ∃ (f : 𝕜 → 𝕜) (hf : MeromorphicAt f a), mk f hf = φ := by
  obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
  exact ⟨f, hf, Subtype.ext hφ⟩

@[simp]
theorem mk_zero : mk (fun _ ↦ (0 : 𝕜)) (.const 0 a) = 0 :=
  Subtype.ext Germ.coe_zero

@[simp]
theorem mk_one : mk (fun _ ↦ (1 : 𝕜)) (.const 1 a) = 1 :=
  Subtype.ext Germ.coe_one

@[simp]
theorem mk_add {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f a) (hg : MeromorphicAt g a) :
    mk (f + g) (hf.add hg) = mk f hf + mk g hg :=
  Subtype.ext (Germ.coe_add f g)

@[simp]
theorem mk_mul {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f a) (hg : MeromorphicAt g a) :
    mk (f * g) (hf.mul hg) = mk f hf * mk g hg :=
  Subtype.ext (Germ.coe_mul f g)

/-- The local coordinate germ vanishing at the centre. -/
def coordinate (a : 𝕜) : meromorphicGerms 𝕜 a :=
  mk (fun z ↦ z - a) ((MeromorphicAt.id a).sub (.const a a))

@[simp]
theorem coe_coordinate :
    ((coordinate a : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (fun z ↦ z - a : 𝕜 → 𝕜) := (rfl)

/-- Scalars act on meromorphic germs through constant functions. -/
instance : Algebra 𝕜 (meromorphicGerms 𝕜 a) :=
  RingHom.toAlgebra
    { toFun c := ⟨Germ.const c,
        mem_meromorphicGerms_iff.mpr ⟨fun _ ↦ c, MeromorphicAt.const c a, rfl⟩⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl }

@[simp, norm_cast]
theorem coe_algebraMap (c : 𝕜) :
    ((algebraMap 𝕜 (meromorphicGerms 𝕜 a) c : meromorphicGerms 𝕜 a) :
      Germ (𝓝[≠] a) 𝕜) = Germ.const c := (rfl)

@[simp]
theorem mk_const (c : 𝕜) : mk (fun _ ↦ c) (.const c a) = algebraMap 𝕜 _ c :=
  -- Germ.const is defined as the germ of the constant function.
  Subtype.ext (rfl)

@[simp, norm_cast]
theorem coe_smul (c : 𝕜) (φ : meromorphicGerms 𝕜 a) :
    ((c • φ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      c • (φ : Germ (𝓝[≠] a) 𝕜) := by
  obtain ⟨f, _, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
  rw [Algebra.smul_def, Subring.coe_mul, coe_algebraMap, ← hφ, ← Germ.coe_smul]
  -- Germ.const c is definitionally the germ of the function fun _ ↦ c.
  exact (Germ.coe_mul (fun _ ↦ c) f).symm.trans
    (Germ.coe_eq.mpr (.of_forall fun _ ↦ by simp [smul_eq_mul]))

@[simp]
theorem mk_smul (c : 𝕜) {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) :
    mk (c • f) (hf.const_smul c) = c • mk f hf := by
  apply Subtype.ext
  simp only [coe_mk, coe_smul, Germ.coe_smul]

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

@[simp]
theorem mk_inv {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) :
    mk f⁻¹ hf.inv = (mk f hf)⁻¹ := by
  apply Subtype.ext
  simp only [coe_mk, coe_inv, Germ.coe_inv]

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
  -- Constant rational casts keep rational scalar multiplication compatible with the algebra.
  nnratCast q := algebraMap 𝕜 _ (q : 𝕜)
  nnratCast_def q := by
    -- Default division is multiplication by the pointwise inverse. Germ.const is the germ of
    -- a constant function by definition, so Germ.coe_eq reduces the goal to scalar arithmetic.
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact .of_forall fun _ ↦ by simpa [div_eq_mul_inv] using (NNRat.cast_def q : (q : 𝕜) = _)
  ratCast q := algebraMap 𝕜 _ (q : 𝕜)
  ratCast_def q := by
    -- Default division is multiplication by the pointwise inverse. Germ.const is the germ of
    -- a constant function by definition, so Germ.coe_eq reduces the goal to scalar arithmetic.
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact .of_forall fun _ ↦ by simpa [div_eq_mul_inv] using (Rat.cast_def q : (q : 𝕜) = _)
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
