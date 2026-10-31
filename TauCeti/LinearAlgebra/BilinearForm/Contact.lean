/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Contact covectors

A covector `a` on a vector space `V` is **contact** for a bilinear form `B` when `a ≠ 0` and `B`
restricts to a nondegenerate form on the hyperplane `ker a`
(`Module.Dual.IsContact`). This is the pointwise linear algebra of a contact form on a manifold:
a one-form `α` is contact exactly when, at every point `x`, the covector `α_x` is contact for the
bilinear form `dα_x`.

The condition only depends on `B` through its values on `ker a × ker a`
(`Module.Dual.isContact_congr`), and is unchanged when `a` or `B` is multiplied by a nonzero
scalar. Together these give the pointwise form of the rescaling law for contact forms: since
`d(f α) = df ∧ α + f dα`, and `df ∧ α` vanishes on `ker α × ker α`, the forms `α` and `f α` are
contact together whenever `f` vanishes nowhere.

For an alternating `B`, the hyperplane `ker a` carries a nondegenerate alternating form, so it has
even dimension and `V` has odd dimension (`Module.Dual.IsContact.odd_finrank`).

Contact covectors arise on hyperplanes transverse to a vector. If `B` is nondegenerate and
alternating, `L : U → V` is injective and `z` is a vector outside the range of `L` which together
with it spans `V`, then `u ↦ B z (L u)` is contact for the restriction `B (L ·) (L ·)` of `B` to
`U` (`Module.Dual.isContact_comp_compl₁₂`). This is the pointwise reason why the primitive
`ι_Z ω` of a symplectic form restricts to a contact form on a hypersurface transverse to `Z`.

For an alternating `B` and a contact covector `a`, the bilinear form `B + a ⊗ a`,
`(v, w) ↦ B v w + a v * a w`, is left-separating
(`Module.Dual.IsContact.separatingLeft_add_smulRight`), so in finite dimension `v ↦ B v + a(v) a`
is an isomorphism onto the dual. This is the pointwise contact flat map `X ↦ ι_X dα + α(X) α` of a
contact form. The preimage of `a` itself is characterized by the Reeb equations: `B r + a(r) a = a`
exactly when `a r = 1` and `B r = 0` (`Module.Dual.IsContact.add_smulRight_apply_eq_self_iff`).

## Main declarations

* `Module.Dual.IsContact`: `a ≠ 0` and `B` is nondegenerate on `ker a`.
* `Module.Dual.isContact_iff_of_isRefl`: for a reflexive `B`, the elementwise criterion: the only
  vector of `ker a` which is `B`-orthogonal to all of `ker a` is zero.
* `Module.Dual.isContact_congr`, `Module.Dual.isContact_smul_iff`,
  `Module.Dual.isContact_smul_bilinForm_iff`: invariance under changes of `B` off `ker a` and
  under nonzero rescaling of `a` and of `B`.
* `Module.Dual.IsContact.even_finrank_ker`, `Module.Dual.IsContact.odd_finrank`: the dimension
  count.
* `Module.Dual.isContact_comp_compl₁₂`: the covector `B z` restricted to a hyperplane transverse to
  `z` is contact for the restriction of a nondegenerate alternating `B`.
* `Module.Dual.IsContact.separatingLeft_add_smulRight`: `B + a ⊗ a` is left-separating.
* `Module.Dual.IsContact.add_smulRight_apply_eq_self_iff`: the preimage of `a` under
  `v ↦ B v + a(v) a`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public section

open Module

namespace Module.Dual

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {a : Module.Dual K V} {B B' : LinearMap.BilinForm K V}

/-- A covector `a` is **contact** for a bilinear form `B` when it is nonzero and `B` restricts to a
nondegenerate bilinear form on the hyperplane `ker a`. For a one-form `α` on a manifold, the
covector `α_x` being contact for `dα_x` at every point `x` is the contact condition. -/
def IsContact (a : Module.Dual K V) (B : LinearMap.BilinForm K V) : Prop :=
  a ≠ 0 ∧ (B.restrict (LinearMap.ker a)).Nondegenerate

theorem isContact_def :
    a.IsContact B ↔ a ≠ 0 ∧ (B.restrict (LinearMap.ker a)).Nondegenerate :=
  Iff.rfl

/-- A contact covector is nonzero. -/
theorem IsContact.ne_zero (h : a.IsContact B) : a ≠ 0 :=
  h.1

/-- A contact covector's bilinear form is nondegenerate on its kernel. -/
theorem IsContact.nondegenerate_restrict (h : a.IsContact B) :
    (B.restrict (LinearMap.ker a)).Nondegenerate :=
  h.2

/-- For a reflexive bilinear form, and in particular for an alternating one, a covector `a` is
contact exactly when it is nonzero and no nonzero vector of `ker a` is `B`-orthogonal to all of
`ker a`. -/
theorem isContact_iff_of_isRefl (hB : B.IsRefl) :
    a.IsContact B ↔
      a ≠ 0 ∧ ∀ v, a v = 0 → (∀ w, a w = 0 → B v w = 0) → v = 0 := by
  have hrefl : (B.restrict (LinearMap.ker a)).IsRefl := fun v w h ↦ hB v w h
  rw [isContact_def, LinearMap.BilinForm.Nondegenerate,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl]
  refine and_congr_right fun _ ↦ ⟨fun h v hv hvw ↦ ?_, fun h v hv ↦ ?_⟩
  · have := h ⟨v, hv⟩ fun w ↦ hvw w w.2
    simpa using congrArg Subtype.val this
  · exact Subtype.ext <| h v v.2 fun w hw ↦ hv ⟨w, hw⟩

/-- Whether `a` is contact for `B` only depends on the values of `B` on `ker a × ker a`. -/
theorem isContact_congr (h : ∀ v w, a v = 0 → a w = 0 → B v w = B' v w) :
    a.IsContact B ↔ a.IsContact B' := by
  have hrestrict : B.restrict (LinearMap.ker a) = B'.restrict (LinearMap.ker a) := by
    ext v w
    exact h v w v.2 w.2
  rw [isContact_def, isContact_def, hrestrict]

/-- A nonzero multiple of a covector is contact for `B` exactly when the covector is. -/
@[simp]
theorem isContact_smul_iff {c : K} (hc : c ≠ 0) : (c • a).IsContact B ↔ a.IsContact B := by
  rw [isContact_def, isContact_def, LinearMap.ker_smul _ _ hc, smul_ne_zero_iff_right hc]

/-- A covector is contact for a nonzero multiple of `B` exactly when it is contact for `B`. -/
@[simp]
theorem isContact_smul_bilinForm_iff {c : K} (hc : c ≠ 0) :
    a.IsContact (c • B) ↔ a.IsContact B := by
  have hrestrict : (c • B).restrict (LinearMap.ker a) = c • B.restrict (LinearMap.ker a) := by
    ext v w
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.smul_apply]
  rw [isContact_def, isContact_def, hrestrict,
    TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)]

/-- For an alternating `B`, the kernel of a contact covector has even dimension. -/
theorem IsContact.even_finrank_ker [FiniteDimensional K V] (hB : B.IsAlt) (h : a.IsContact B) :
    Even (finrank K (LinearMap.ker a)) :=
  LinearMap.BilinForm.IsAlt.even_finrank (B := B.restrict (LinearMap.ker a))
    (fun v ↦ hB v) h.nondegenerate_restrict

/-- A finite-dimensional space carrying a covector which is contact for an alternating bilinear
form has odd dimension. -/
theorem IsContact.odd_finrank [FiniteDimensional K V] (hB : B.IsAlt) (h : a.IsContact B) :
    Odd (finrank K V) := by
  rw [← finrank_ker_add_one_of_ne_zero h.ne_zero]
  exact (h.even_finrank_ker hB).add_one

/-! ### Hyperplanes transverse to a vector -/

/-- **Transverse hyperplanes of a nondegenerate alternating form carry contact covectors.** Let
`B` be a nondegenerate alternating form on `V`, let `L : U → V` be injective, and let `z` be a
vector outside the range of `L` which together with it spans `V`, so that `L` identifies `U` with
a hyperplane transverse to `z`. Then the covector `u ↦ B z (L u)` on `U` is contact for the
restricted form `B (L ·) (L ·)`.

This is the linear algebra behind hypersurfaces of contact type: when `ι_Z ω = α` for a vector
field `Z` transverse to a hypersurface, the restriction of `α` to the hypersurface is a contact
form. -/
theorem isContact_comp_compl₁₂ {U : Type*} [AddCommGroup U] [Module K U] (hB : B.IsAlt)
    (hB' : B.SeparatingLeft) {L : U →ₗ[K] V} (hL : Function.Injective L) {z : V}
    (hz : z ∉ LinearMap.range L) (hLz : LinearMap.range L ⊔ K ∙ z = ⊤) :
    IsContact ((B z).comp L) (B.compl₁₂ L L) := by
  have hdecomp (v : V) : ∃ u : U, ∃ c : K, L u + c • z = v := by
    obtain ⟨_, ⟨u, rfl⟩, _, hw, h⟩ := Submodule.mem_sup.1 (hLz ▸ Submodule.mem_top : v ∈ _)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨u, c, h⟩
  have hzL (u : U) : B (L u) z = -B z (L u) := (hB.neg_eq z (L u)).symm
  -- The covector does not vanish: otherwise `B z` would vanish on `range L` and on `z`.
  have hne : (B z).comp L ≠ 0 := by
    intro h
    refine hz (hB' z (fun v ↦ ?_) ▸ Submodule.zero_mem _)
    obtain ⟨u, c, rfl⟩ := hdecomp v
    simpa [hB z] using LinearMap.congr_fun h u
  refine (isContact_iff_of_isRefl (B := B.compl₁₂ L L)
    fun x y hxy ↦ hB.isRefl (L x) (L y) hxy).2 ⟨hne, ?_⟩
  intro u hu huw
  simp only [LinearMap.comp_apply, LinearMap.compl₁₂_apply] at hu huw
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, B z (L u₁) ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext h)
  -- `B (L u)` vanishes on `ker (B z)`, so it is the multiple `c • B z`.
  set c := B (L u) (L u₁) / B z (L u₁)
  have hc : L u - c • z = 0 := by
    refine hB' _ fun v ↦ ?_
    obtain ⟨w, d, rfl⟩ := hdecomp v
    have hw := huw (w - (B z (L w) / B z (L u₁)) • u₁) (by
      simp [div_mul_cancel₀ _ hu₁])
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      map_add, hzL, hu, hB z] at hw ⊢
    rw [sub_eq_zero] at hw
    rw [hw]
    simp only [c]
    field_simp
    ring
  -- Hence `L u` is a multiple of `z`, which lies outside `range L` unless the multiple is zero.
  have hc0 : c = 0 := by
    by_contra hc0
    refine hz ⟨c⁻¹ • u, ?_⟩
    rw [map_smul, sub_eq_zero.1 hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hc0, zero_smul, sub_zero] at hc
  exact hL (hc.trans (map_zero L).symm)

/-! ### The contact flat map -/

/-- For an alternating `B` and a contact covector `a`, the bilinear form `B + a ⊗ a`,
`(v, w) ↦ B v w + a v * a w`, is left-separating. This is the linear algebra behind the
contact flat map `v ↦ ι_v dα + α(v) α` of a contact form, which is invertible in finite
dimension. -/
theorem IsContact.separatingLeft_add_smulRight (hB : B.IsAlt) (h : a.IsContact B) :
    (B + a.smulRight a).SeparatingLeft := by
  intro v hv
  have hvv : a v = 0 := by
    simpa [hB v] using hv v
  refine Subtype.ext_iff.1 (h.nondegenerate_restrict.1 ⟨v, hvv⟩ fun w ↦ ?_)
  simpa [w.2] using hv w

/-- For an alternating `B` and a contact covector `a`, a vector `r` solves `B r + a(r) a = a`
exactly when `a r = 1` and `r` is `B`-orthogonal to everything: these are the Reeb equations. -/
theorem IsContact.add_smulRight_apply_eq_self_iff (hB : B.IsAlt) (h : a.IsContact B) {r : V} :
    (B + a.smulRight a) r = a ↔ a r = 1 ∧ B r = 0 := by
  refine ⟨fun hr ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by ext w; simp [h₁, h₂]⟩
  have hr' (w : V) : B r w + a r * a w = a w := by
    simpa using LinearMap.congr_fun hr w
  -- Evaluating at `r` itself gives `a r * a r = a r`, so `a r` is `0` or `1`.
  have hrr : a r * a r = a r := by
    simpa [hB r] using hr' r
  have h₁ : a r = 1 := by
    by_cases h₀ : a r = 0
    · -- If `a r = 0`, then `r ∈ ker a` is `B`-orthogonal to `ker a`, so `r = 0` and `a = 0`.
      have hr₀ : r = 0 := Subtype.ext_iff.1 <| h.nondegenerate_restrict.1 ⟨r, h₀⟩ fun w ↦ by
        simpa [h₀, w.2] using hr' w
      exact absurd (LinearMap.ext fun w ↦ by simpa [hr₀] using (hr' w).symm) h.ne_zero
    · exact (mul_eq_left₀ h₀).1 hrr
  exact ⟨h₁, LinearMap.ext fun w ↦ by simpa [h₁] using hr' w⟩

end Module.Dual
