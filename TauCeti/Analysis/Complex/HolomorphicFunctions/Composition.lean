/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ

/-!
# Composition of holomorphic functions and germs

If `f` is holomorphic on an open set `U` and maps a subset `s ⊆ U` into an open set `V`, then
`HolomorphicFunctions.preimageOpen f V` is an open subset `U' ≤ U` containing `s` that `extend f`
maps into `V`. Composing `g : holomorphicFunctions V` with `f` on any such `U'` gives
`HolomorphicFunctions.comp g f hU' hmaps : holomorphicFunctions U'`.

At the level of germs, if `f : holomorphicGerms s` has `spectrum ℂ f ⊆ t` (meaning all values of
`f` on `s` lie in `t`), composing `g : holomorphicGerms t` with `f` produces a well-defined germ
`holomorphicGerms.comp g f ht : holomorphicGerms s`, compatible with ambient representatives,
open-domain composition, and pointwise evaluation.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

variable {s : Set ℂ} {U U' U'' V V' : Opens ℂ}

/-- The open subset of `U` where `f` takes values in `V`. -/
def preimageOpen (f : holomorphicFunctions U) (V : Opens ℂ) : Opens ℂ where
  carrier := Subtype.val '' (f.val ⁻¹' (V : Set ℂ))
  is_open' := U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage f.val.continuous)

/-- A point lies in `preimageOpen f V` iff it lies in `U` and `extend f` sends it into `V`. -/
@[simp]
theorem mem_preimageOpen {f : holomorphicFunctions U} {V : Opens ℂ} {z : ℂ} :
    z ∈ preimageOpen f V ↔ z ∈ U ∧ extend f z ∈ V := by
  constructor
  · rintro ⟨⟨z, hz⟩, hV, rfl⟩
    refine ⟨hz, ?_⟩
    rw [extend_apply f ⟨z, hz⟩]
    exact hV
  · rintro ⟨hz, hV⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    change f.val ⟨z, hz⟩ ∈ V
    rwa [← extend_apply f ⟨z, hz⟩]

/-- The preimage open domain is contained in the source domain of `f`. -/
theorem preimageOpen_le (f : holomorphicFunctions U) (V : Opens ℂ) : preimageOpen f V ≤ U :=
  fun _ hz => (mem_preimageOpen.mp hz).1

/-- Extending `f` by zero maps `preimageOpen f V` into `V`. -/
theorem mapsTo_extend_preimageOpen (f : holomorphicFunctions U) (V : Opens ℂ) :
    MapsTo (extend f) (preimageOpen f V) V :=
  fun _ hz => (mem_preimageOpen.mp hz).2

/-- Any subset of `U` mapped into `V` by `extend f` lies in `preimageOpen f V`. -/
theorem subset_preimageOpen {f : holomorphicFunctions U} {V : Opens ℂ}
    (hsU : s ⊆ U) (hsV : MapsTo (extend f) s V) : s ⊆ preimageOpen f V :=
  fun _ hz => mem_preimageOpen.mpr ⟨hsU hz, hsV hz⟩

/-- Compose `g : holomorphicFunctions V` with `f : holomorphicFunctions U` on an open
subset `U' ≤ U` mapped into `V` by `extend f`. -/
def comp (g : holomorphicFunctions V) (f : holomorphicFunctions U)
    (hU' : U' ≤ U) (hmaps : MapsTo (extend f) U' V) : holomorphicFunctions U' :=
  of U' (extend g ∘ extend f)
    ((differentiableOn_extend g).comp ((differentiableOn_extend f).mono hU') hmaps)

/-- Pointwise evaluation of `comp g f hU' hmaps` on `U'`. -/
@[simp]
theorem comp_apply (g : holomorphicFunctions V) (f : holomorphicFunctions U)
    (hU' : U' ≤ U) (hmaps : MapsTo (extend f) U' V) (z : U') :
    (comp g f hU' hmaps).val z = extend g (extend f z) := by
  rw [comp, of_apply]
  rfl

/-- Composition of restricted ambient holomorphic functions agrees with ambient composition. -/
@[simp]
theorem comp_of {φ ψ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ V) (hψ : DifferentiableOn ℂ ψ U)
    (hU' : U' ≤ U) (hmaps : MapsTo ψ U' V) :
    comp (of V φ hφ) (of U ψ hψ) hU'
      (show MapsTo (extend (of U ψ hψ)) U' V from fun z hz => by
        rw [extend_apply _ ⟨z, hU' hz⟩, of_apply]
        exact hmaps hz) =
      of U' (φ ∘ ψ) (hφ.comp (hψ.mono hU') hmaps) := by
  apply Subtype.ext
  ext z
  have hzV : ψ z ∈ V := hmaps z.property
  rw [comp_apply, of_apply, Function.comp_apply, extend_apply _ ⟨(z : ℂ), hU' z.property⟩,
    of_apply, extend_apply _ ⟨ψ z, hzV⟩, of_apply]

/-- Shrinking the domain of a composite restricts the composite. -/
@[simp]
theorem comp_mono (g : holomorphicFunctions V) (f : holomorphicFunctions U)
    (hU' : U' ≤ U) (hmaps : MapsTo (extend f) U' V) (hU'' : U'' ≤ U') :
    restrict hU'' (comp g f hU' hmaps) =
      comp g f (hU''.trans hU') (hmaps.mono_left hU'') := by
  apply Subtype.ext
  ext z
  rw [restrict_apply, comp_apply, comp_apply]

/-- Composing with a restricted outer function leaves the composite unchanged. -/
@[simp]
theorem comp_restrict_left (g : holomorphicFunctions V) (f : holomorphicFunctions U)
    (hV' : V' ≤ V) (hU' : U' ≤ U) (hmaps : MapsTo (extend f) U' V') :
    comp (restrict hV' g) f hU' hmaps = comp g f hU' (hmaps.mono_right hV') := by
  apply Subtype.ext
  ext z
  have hzV' : extend f z ∈ V' := hmaps z.property
  rw [comp_apply, comp_apply, extend_apply _ ⟨extend f z, hzV'⟩, restrict_apply,
    extend_apply g ⟨extend f z, hV' hzV'⟩]

/-- Composing with a restricted inner function leaves the composite unchanged. -/
@[simp]
theorem comp_restrict_right (g : holomorphicFunctions V) (f : holomorphicFunctions U)
    (hU₁ : U' ≤ U) (hU₂ : U'' ≤ U') (hmaps : MapsTo (extend (restrict hU₁ f)) U'' V) :
    comp g (restrict hU₁ f) hU₂ hmaps =
      comp g f (hU₂.trans hU₁)
        (show MapsTo (extend f) U'' V from fun z hz => by
          have hz' := hmaps hz
          rw [extend_apply _ ⟨z, hU₂ hz⟩, restrict_apply] at hz'
          simpa only [extend_apply f ⟨z, hU₁ (hU₂ hz)⟩] using hz') := by
  apply Subtype.ext
  ext z
  rw [comp_apply, comp_apply, extend_apply _ ⟨(z : ℂ), hU₂ z.property⟩, restrict_apply,
    extend_apply f ⟨(z : ℂ), hU₁ (hU₂ z.property)⟩]

end TauCeti.HolomorphicFunctions

namespace TauCeti.holomorphicGerms

variable {s t : Set ℂ}

/-- If the spectrum of a germ `f` near `s` is contained in `t`, every value of `f` on `s`
belongs to `t`. -/
theorem eval_mem_of_spectrum_subset {f : holomorphicGerms s} (ht : spectrum ℂ f ⊆ t)
    {x : ℂ} (hx : x ∈ s) : eval x hx f ∈ t :=
  ht ((spectrum_eq f).symm ▸ ⟨x, hx, rfl⟩)

private theorem exists_comp_value (g : holomorphicGerms t) (f : holomorphicGerms s)
    (ht : spectrum ℂ f ⊆ t) :
    ∃ h : holomorphicGerms s,
      ∀ (φ ψ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ t) (hψ : AnalyticOnNhd ℂ ψ s)
        (_ : ofFun φ hφ = g) (hf : ofFun ψ hψ = f),
          ofFun (φ ∘ ψ) (fun x hx => by
            have hx_t : ψ x ∈ t := by
              have hmem := eval_mem_of_spectrum_subset ht hx
              rwa [← hf, eval_ofFun] at hmem
            exact (hφ (ψ x) hx_t).comp (hψ x hx)) = h := by
  obtain ⟨φ₀, hφ₀, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ₀, hψ₀, rfl⟩ := exists_ofFun_eq f
  have hmaps₀ : MapsTo ψ₀ s t := fun x hx => by
    simpa only [eval_ofFun] using eval_mem_of_spectrum_subset ht hx
  refine ⟨ofFun (φ₀ ∘ ψ₀) (hφ₀.comp hψ₀ hmaps₀), fun φ ψ hφ hψ hg hf => ?_⟩
  apply (ofFun_eq_iff _ _).mpr
  obtain ⟨V, hVopen, htV, hφeq⟩ := eventually_nhdsSet_iff_exists.mp ((ofFun_eq_iff hφ hφ₀).mp hg)
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  have hψeq : ψ =ᶠ[𝓝 x] ψ₀ := ((ofFun_eq_iff hψ hψ₀).mp hf).filter_mono (nhds_le_nhdsSet hx)
  have hψ₀V : ∀ᶠ z in 𝓝 x, ψ₀ z ∈ V :=
    (hψ₀ x hx).continuousAt.eventually (hVopen.mem_nhds (htV (hmaps₀ hx)))
  filter_upwards [hψeq, hψ₀V] with z hz₁ hz₂
  simp only [Function.comp_apply, hz₁, hφeq _ hz₂]

/-- Compose a holomorphic germ `g` near `t` with a holomorphic germ `f` near `s` when
`spectrum ℂ f ⊆ t` (that is, every value of `f` on `s` belongs to `t`). -/
def comp (g : holomorphicGerms t) (f : holomorphicGerms s) (ht : spectrum ℂ f ⊆ t) :
    holomorphicGerms s :=
  Classical.choose (exists_comp_value g f ht)

/-- Composing ambient holomorphic representatives gives the germ of their function composite. -/
@[simp]
theorem comp_ofFun {φ ψ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ t) (hψ : AnalyticOnNhd ℂ ψ s)
    (ht : spectrum ℂ (ofFun ψ hψ) ⊆ t) :
    comp (ofFun φ hφ) (ofFun ψ hψ) ht =
      ofFun (φ ∘ ψ) (hφ.comp hψ (mapsTo_iff_image_subset.mpr ((spectrum_ofFun ψ hψ) ▸ ht))) :=
  (Classical.choose_spec (exists_comp_value (ofFun φ hφ) (ofFun ψ hψ) ht)
    φ ψ hφ hψ rfl rfl).symm

/-- Germ composition agrees with open-domain composition on any compatible open subset. -/
theorem comp_toGerm {U U' V : Opens ℂ} (hs : s ⊆ U) (ht : t ⊆ V)
    (g : holomorphicFunctions V) (f : holomorphicFunctions U)
    (hU' : U' ≤ U) (hs' : s ⊆ U') (hmaps : MapsTo (HolomorphicFunctions.extend f) U' V)
    (ht_spec : spectrum ℂ (HolomorphicFunctions.toGerm hs f) ⊆ t) :
    comp (HolomorphicFunctions.toGerm ht g) (HolomorphicFunctions.toGerm hs f) ht_spec =
      HolomorphicFunctions.toGerm hs' (HolomorphicFunctions.comp g f hU' hmaps) := by
  have hf_eq : HolomorphicFunctions.toGerm hs f =
      ofFun (HolomorphicFunctions.extend f) (HolomorphicFunctions.analyticOnNhd_extend hs f) :=
    HolomorphicFunctions.toGerm_eq_ofFun hs f _ _ fun z =>
      (HolomorphicFunctions.extend_apply f z).symm
  have hg_eq : HolomorphicFunctions.toGerm ht g =
      ofFun (HolomorphicFunctions.extend g) (HolomorphicFunctions.analyticOnNhd_extend ht g) :=
    HolomorphicFunctions.toGerm_eq_ofFun ht g _ _ fun z =>
      (HolomorphicFunctions.extend_apply g z).symm
  have ht_spec' : spectrum ℂ
      (ofFun (HolomorphicFunctions.extend f)
        (HolomorphicFunctions.analyticOnNhd_extend hs f)) ⊆ t :=
    hf_eq ▸ ht_spec
  have hcongr : comp (HolomorphicFunctions.toGerm ht g) (HolomorphicFunctions.toGerm hs f) ht_spec =
      comp (ofFun (HolomorphicFunctions.extend g) (HolomorphicFunctions.analyticOnNhd_extend ht g))
        (ofFun (HolomorphicFunctions.extend f) (HolomorphicFunctions.analyticOnNhd_extend hs f))
        ht_spec' := by
    congr 1
  rw [hcongr, comp_ofFun]
  exact (HolomorphicFunctions.toGerm_eq_ofFun hs' _ _ _ fun z =>
    HolomorphicFunctions.comp_apply g f hU' hmaps z).symm

/-- Evaluating a composite germ evaluates the outer germ at the value of the inner germ. -/
@[simp]
theorem eval_comp (g : holomorphicGerms t) (f : holomorphicGerms s)
    (ht : spectrum ℂ f ⊆ t) (x : ℂ) (hx : x ∈ s) :
    eval x hx (comp g f ht) = eval (eval x hx f) (eval_mem_of_spectrum_subset ht hx) g := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq f
  simp only [comp_ofFun, eval_ofFun, Function.comp_apply]

end TauCeti.holomorphicGerms
