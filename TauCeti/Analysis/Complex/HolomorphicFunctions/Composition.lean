/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ

/-!
# Composition of holomorphic functions and germs

Pullback along a holomorphic map `f : holomorphicFunctions U` with values in `V` defines a
continuous algebra homomorphism `HolomorphicFunctions.comp f hf : holomorphicFunctions V →ₐ[ℂ]
holomorphicFunctions U`. Given any open set `V`, `HolomorphicFunctions.preimageOpens f V` is the
open subset of `U` where `f` takes values in `V`.

At the germ level, any `g : holomorphicGerms s` whose spectrum `spectrum ℂ g` (its set of values on
`s`) is contained in `t` induces a pullback homomorphism
`holomorphicGerms.comp g hg : holomorphicGerms t →ₐ[ℂ] holomorphicGerms s`, independent of the
choice of open neighbourhoods and representatives.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

variable {U V W : Opens ℂ}

/-- Pullback of holomorphic functions along a holomorphic map `f` from `U` into `V`. -/
def comp (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ
    (⟨fun z ↦ ⟨f.val z, hf z⟩, f.val.continuous.subtype_mk hf⟩ : C(U, V))).comp
      (holomorphicFunctions V).val).codRestrict (holomorphicFunctions U) fun g ↦ by
    refine mem_holomorphicFunctions_iff_of_eqOn (g := extend g ∘ extend f) (fun z ↦ ?_) |>.mpr ?_
    · simp only [Function.comp_apply, extend_apply f z]
      exact extend_apply g ⟨f.val z, hf z⟩
    · exact (differentiableOn_extend g).comp (differentiableOn_extend f) fun z hz ↦ by
        rw [extend_apply f ⟨z, hz⟩]
        exact hf ⟨z, hz⟩

@[simp]
theorem comp_apply (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V)
    (g : holomorphicFunctions V) (z : U) :
    (comp f hf g).val z = g.val ⟨f.val z, hf z⟩ := (rfl)

/-- Composition of ambient holomorphic representatives commutes with `HolomorphicFunctions.of`. -/
@[simp]
theorem comp_of {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ U)
    (hf : ∀ z : U, (of U φ hφ).val z ∈ V) (ψ : ℂ → ℂ) (hψ : DifferentiableOn ℂ ψ V) :
    comp (of U φ hφ) hf (of V ψ hψ) =
      of U (ψ ∘ φ) (hψ.comp hφ fun z hz ↦
        SetLike.mem_coe.mpr (by simpa only [of_apply] using hf ⟨z, hz⟩)) := by
  apply Subtype.ext
  ext z
  simp

/-- Pulling back the coordinate function along `f` recovers `f`. -/
@[simp]
theorem comp_id_right (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    comp f hf (of V id differentiableOn_id) = f := by
  apply Subtype.ext
  ext z
  simp

/-- Pulling back along the identity on `U` is the identity algebra homomorphism. -/
@[simp]
theorem comp_id_left (hf : ∀ z : U, (of U id differentiableOn_id).val z ∈ U) :
    comp (of U id differentiableOn_id) hf = AlgHom.id ℂ (holomorphicFunctions U) := by
  ext g : 1
  apply Subtype.ext
  ext z
  simp

/-- Pullback along a holomorphic map is continuous in the compact-open topology. -/
@[continuity]
theorem continuous_comp (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    Continuous (comp f hf) := by
  unfold comp
  exact ((ContinuousMap.compRightAlgHom_continuous ℂ ℂ
    (⟨fun z ↦ ⟨f.val z, hf z⟩, f.val.continuous.subtype_mk hf⟩ : C(U, V))).comp
      continuous_subtype_val).subtype_mk _

/-- Restricting a pulled-back holomorphic function is pullback along the restricted map. -/
@[simp]
theorem restrict_comp_apply (hWU : W ≤ U) (f : holomorphicFunctions U)
    (hf : ∀ z : U, f.val z ∈ V) (g : holomorphicFunctions V) :
    restrict hWU (comp f hf g) =
      comp (restrict hWU f) (fun z ↦ by rw [restrict_apply]; exact hf (Set.inclusion hWU z)) g := by
  apply Subtype.ext
  ext z
  simp

/-- Pulling back a restricted holomorphic function is pullback along the ambient inclusion. -/
@[simp]
theorem comp_restrict_apply (hVW : V ≤ W) (f : holomorphicFunctions U)
    (hf : ∀ z : U, f.val z ∈ V) (g : holomorphicFunctions W) :
    comp f hf (restrict hVW g) = comp f (fun z ↦ hVW (hf z)) g := by
  apply Subtype.ext
  ext z
  simp

/-- Pullback of holomorphic functions is functorial under composition. -/
@[simp]
theorem comp_comp (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V)
    (g : holomorphicFunctions V) (hg : ∀ w : V, g.val w ∈ W) (h : holomorphicFunctions W) :
    comp f hf (comp g hg h) =
      comp (comp f hf g) (fun z ↦ by rw [comp_apply]; exact hg ⟨f.val z, hf z⟩) h := by
  apply Subtype.ext
  ext z
  simp

/-- The open subset of `U` on which `f : holomorphicFunctions U` takes values in `V`. -/
def preimageOpens (f : holomorphicFunctions U) (V : Opens ℂ) : Opens ℂ :=
  ⟨Subtype.val '' (f.val ⁻¹' (V : Set ℂ)),
    U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage f.val.continuous)⟩

@[simp]
theorem mem_preimageOpens {f : holomorphicFunctions U} {V : Opens ℂ} {z : ℂ} :
    z ∈ preimageOpens f V ↔ ∃ hz : z ∈ U, f.val ⟨z, hz⟩ ∈ V := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hfz⟩
    exact ⟨⟨z, hz⟩, hfz, rfl⟩

theorem preimageOpens_le (f : holomorphicFunctions U) (V : Opens ℂ) :
    preimageOpens f V ≤ U := by
  intro z hz
  exact (mem_preimageOpens.mp hz).1

theorem restrict_preimageOpens_mem (f : holomorphicFunctions U) (V : Opens ℂ)
    (z : preimageOpens f V) : (restrict (preimageOpens_le f V) f).val z ∈ V := by
  obtain ⟨hz, hfz⟩ := mem_preimageOpens.mp z.property
  simpa only [restrict_apply] using hfz

/-- A subset `s ⊆ U` mapped by `f` into `V` is contained in `preimageOpens f V`. -/
theorem subset_preimageOpens {s : Set ℂ} (hs : s ⊆ U) (f : holomorphicFunctions U)
    (hf : ∀ (z : ℂ) (hz : z ∈ s), f.val ⟨z, hs hz⟩ ∈ V) :
    s ⊆ preimageOpens f V := fun z hz ↦
  mem_preimageOpens.mpr ⟨hs hz, hf z hz⟩

/-- A set `s` lies in `preimageOpens f V` if and only if `s ⊆ U` and `f` maps `s` into `V`. -/
theorem subset_preimageOpens_iff {s : Set ℂ} {f : holomorphicFunctions U} :
    s ⊆ preimageOpens f V ↔ ∃ hs : s ⊆ U, ∀ (z : ℂ) (hz : z ∈ s), f.val ⟨z, hs hz⟩ ∈ V :=
  ⟨fun h ↦ ⟨h.trans (preimageOpens_le f V), fun _ hz ↦ (mem_preimageOpens.mp (h hz)).2⟩,
    fun ⟨hs, hf⟩ ↦ subset_preimageOpens hs f hf⟩

end TauCeti.HolomorphicFunctions

namespace TauCeti.holomorphicGerms

open HolomorphicFunctions

variable {s t u : Set ℂ}

/-- If `spectrum ℂ (toGerm hsU f) ⊆ t` and `t ⊆ V`, then `s` lies in `preimageOpens f V`. -/
theorem subset_preimageOpens_of_spectrum_subset {U V : Opens ℂ} {hsU : s ⊆ U}
    {f : holomorphicFunctions U} (hg : spectrum ℂ (toGerm hsU f) ⊆ t) (htV : t ⊆ V) :
    s ⊆ preimageOpens f V := by
  intro z hz
  refine mem_preimageOpens.mpr ⟨hsU hz, htV (hg ?_)⟩
  rw [spectrum_eq]
  exact ⟨z, hz, eval_toGerm hsU z hz f⟩

private theorem toGerm_comp_preimageOpens_congr {U₁ U₂ V : Opens ℂ} {hs₁ : s ⊆ U₁} {hs₂ : s ⊆ U₂}
    {f₁ : holomorphicFunctions U₁} {f₂ : holomorphicFunctions U₂}
    (hf : toGerm hs₁ f₁ = toGerm hs₂ f₂)
    (hg₁ : spectrum ℂ (toGerm hs₁ f₁) ⊆ t) (hg₂ : spectrum ℂ (toGerm hs₂ f₂) ⊆ t)
    (htV : t ⊆ V) (ψ : holomorphicFunctions V) :
    toGerm (subset_preimageOpens_of_spectrum_subset hg₁ htV)
      (HolomorphicFunctions.comp (HolomorphicFunctions.restrict (preimageOpens_le f₁ V) f₁)
        (restrict_preimageOpens_mem f₁ V) ψ) =
    toGerm (subset_preimageOpens_of_spectrum_subset hg₂ htV)
      (HolomorphicFunctions.comp (HolomorphicFunctions.restrict (preimageOpens_le f₂ V) f₂)
        (restrict_preimageOpens_mem f₂ V) ψ) := by
  obtain ⟨W, hsW, hWU₁, hWU₂, hW_eq⟩ := (toGerm_eq_iff hs₁ hs₂ f₁ f₂).mp hf
  let W' : Opens ℂ := W ⊓ preimageOpens f₁ V ⊓ preimageOpens f₂ V
  have hsW' : s ⊆ W' := fun z hz ↦
    ⟨⟨hsW hz, subset_preimageOpens_of_spectrum_subset hg₁ htV hz⟩,
      subset_preimageOpens_of_spectrum_subset hg₂ htV hz⟩
  have hW'₁ : W' ≤ preimageOpens f₁ V := fun _ hz ↦ hz.1.2
  have hW'₂ : W' ≤ preimageOpens f₂ V := fun _ hz ↦ hz.2
  refine (toGerm_eq_iff _ _ _ _).mpr ⟨W', hsW', hW'₁, hW'₂, ?_⟩
  apply Subtype.ext
  ext z
  have hz_eq := congrArg (fun k : holomorphicFunctions W ↦ k.val ⟨z, z.property.1.1⟩) hW_eq
  simp only [HolomorphicFunctions.restrict_apply, HolomorphicFunctions.comp_apply] at hz_eq ⊢
  congr 1
  exact Subtype.ext hz_eq

/-- Pullback of holomorphic germs near `t` along a holomorphic germ `g` near `s` whose spectrum
is contained in `t`. -/
def comp (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t) :
    holomorphicGerms t →ₐ[ℂ] holomorphicGerms s :=
  let hsU := (exists_toGerm_eq g).choose_spec.choose
  let f := (exists_toGerm_eq g).choose_spec.choose_spec.choose
  have hf : toGerm hsU f = g := (exists_toGerm_eq g).choose_spec.choose_spec.choose_spec
  have hgf : spectrum ℂ (toGerm hsU f) ⊆ t := hf.symm ▸ hg
  lift
    (fun V htV ↦ (toGerm (subset_preimageOpens_of_spectrum_subset hgf htV)).comp
      (HolomorphicFunctions.comp (HolomorphicFunctions.restrict (preimageOpens_le f V) f)
        (restrict_preimageOpens_mem f V)))
    (fun V₁ V₂ htV₂ hV₂₁ ψ ↦ by
      simp only [AlgHom.comp_apply]
      have hle : preimageOpens f V₂ ≤ preimageOpens f V₁ := fun z hz ↦ by
        obtain ⟨hzU, hfz⟩ := mem_preimageOpens.mp hz
        exact mem_preimageOpens.mpr ⟨hzU, hV₂₁ hfz⟩
      rw [← toGerm_restrict (subset_preimageOpens_of_spectrum_subset hgf htV₂) hle]
      congr 1
      apply Subtype.ext
      ext z
      simp)

/-- Germ composition agrees with open-domain composition on any pair of open representatives. -/
@[simp]
theorem comp_toGerm {U V : Opens ℂ} (hsU : s ⊆ U) (htV : t ⊆ V)
    (f : holomorphicFunctions U) (hfV : ∀ z : U, f.val z ∈ V)
    (hg : spectrum ℂ (toGerm hsU f) ⊆ t) (ψ : holomorphicFunctions V) :
    comp (toGerm hsU f) hg (toGerm htV ψ) =
      toGerm hsU (HolomorphicFunctions.comp f hfV ψ) := by
  let hsU₀ := (exists_toGerm_eq (toGerm hsU f)).choose_spec.choose
  let f₀ := (exists_toGerm_eq (toGerm hsU f)).choose_spec.choose_spec.choose
  have hf₀ : toGerm hsU₀ f₀ = toGerm hsU f :=
    (exists_toGerm_eq (toGerm hsU f)).choose_spec.choose_spec.choose_spec
  calc comp (toGerm hsU f) hg (toGerm htV ψ)
      = toGerm (subset_preimageOpens_of_spectrum_subset (hf₀.symm ▸ hg) htV)
          (HolomorphicFunctions.comp (HolomorphicFunctions.restrict (preimageOpens_le f₀ V) f₀)
            (restrict_preimageOpens_mem f₀ V) ψ) := by
          unfold comp
          exact lift_toGerm _ _ V htV ψ
    _ = toGerm (subset_preimageOpens_of_spectrum_subset hg htV)
          (HolomorphicFunctions.comp (HolomorphicFunctions.restrict (preimageOpens_le f V) f)
            (restrict_preimageOpens_mem f V) ψ) :=
          toGerm_comp_preimageOpens_congr hf₀ (hf₀.symm ▸ hg) hg htV ψ
    _ = toGerm hsU (HolomorphicFunctions.comp f hfV ψ) := by
          refine (toGerm_eq_iff _ _ _ _).mpr ⟨preimageOpens f V,
            subset_preimageOpens_of_spectrum_subset hg htV, le_rfl, preimageOpens_le f V, ?_⟩
          apply Subtype.ext
          ext z
          simp

private theorem comp_congr_left {g₁ g₂ : holomorphicGerms s} (h : g₁ = g₂)
    {hg₁ : spectrum ℂ g₁ ⊆ t} {hg₂ : spectrum ℂ g₂ ⊆ t} (k : holomorphicGerms t) :
    comp g₁ hg₁ k = comp g₂ hg₂ k := by
  subst h
  rfl

/-- Germ composition on ambient analytic functions is ordinary function composition. -/
@[simp]
theorem comp_ofFun {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s)
    (hg : spectrum ℂ (ofFun f hf) ⊆ t) (ψ : ℂ → ℂ) (hψ : AnalyticOnNhd ℂ ψ t) :
    comp (ofFun f hf) hg (ofFun ψ hψ) =
      ofFun (ψ ∘ f)
        (hψ.comp hf (mapsTo_iff_image_subset.mpr ((spectrum_ofFun f hf).symm ▸ hg))) := by
  let V : Opens ℂ := ⟨{w | AnalyticAt ℂ ψ w}, isOpen_analyticAt ℂ ψ⟩
  have htV : t ⊆ V := hψ
  have hψV : DifferentiableOn ℂ ψ V := fun w hw ↦ hw.differentiableAt.differentiableWithinAt
  let U₀ : Opens ℂ := ⟨{z | AnalyticAt ℂ f z}, isOpen_analyticAt ℂ f⟩
  have hsU₀ : s ⊆ U₀ := hf
  have hfU₀ : DifferentiableOn ℂ f U₀ := fun z hz ↦ hz.differentiableAt.differentiableWithinAt
  let f_hol : holomorphicFunctions U₀ := of U₀ f hfU₀
  let U : Opens ℂ := preimageOpens f_hol V
  have hsU : s ⊆ U := by
    intro z hz
    refine mem_preimageOpens.mpr ⟨hsU₀ hz, ?_⟩
    rw [of_apply]
    exact htV (hg ((spectrum_ofFun f hf).symm ▸ mem_image_of_mem f hz))
  have hfU : DifferentiableOn ℂ f U := hfU₀.mono (preimageOpens_le f_hol V)
  have hfV : ∀ z : U, (of U f hfU).val z ∈ V := fun z ↦ by
    obtain ⟨hz, hfz⟩ := mem_preimageOpens.mp z.property
    simpa only [of_apply, f_hol] using hfz
  have hgf : ofFun f hf = toGerm hsU (of U f hfU) := (toGerm_of hsU f hfU).symm
  have hgψ : ofFun ψ hψ = toGerm htV (of V ψ hψV) := (toGerm_of htV ψ hψV).symm
  have hg' : spectrum ℂ (toGerm hsU (of U f hfU)) ⊆ t := hgf ▸ hg
  calc comp (ofFun f hf) hg (ofFun ψ hψ)
      = comp (toGerm hsU (of U f hfU)) hg' (toGerm htV (of V ψ hψV)) := by
          rw [hgψ]
          exact comp_congr_left hgf _
    _ = toGerm hsU (HolomorphicFunctions.comp (of U f hfU) hfV (of V ψ hψV)) :=
          comp_toGerm hsU htV (of U f hfU) hfV hg' (of V ψ hψV)
    _ = ofFun (ψ ∘ f) _ := by
          rw [comp_of, toGerm_of]

/-- Pulling back the coordinate germ along `g` recovers `g`. -/
@[simp]
theorem comp_ofFun_id (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t) :
    comp g hg (ofFun id analyticOnNhd_id) = g := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  rw [comp_ofFun]
  rfl

/-- Evaluating a composed germ at a point of `s` evaluates the outer germ at `eval x hx g`. -/
@[simp]
theorem eval_comp (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms t) (x : ℂ) (hx : x ∈ s) :
    eval x hx (comp g hg k) =
      eval (eval x hx g) (hg (by rw [spectrum_eq]; exact ⟨x, hx, rfl⟩)) k := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  simp

/-- Pulling back a restricted germ is pullback along the ambient inclusion. -/
@[simp]
theorem comp_restrict (htu : t ⊆ u) (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms u) :
    comp g hg (restrict htu k) = comp g (hg.trans htu) k := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  simp

/-- Pulling back germs along the coordinate germ on `s` is the identity algebra homomorphism. -/
@[simp]
theorem comp_id_left (hg : spectrum ℂ (ofFun id (analyticOnNhd_id (s := s))) ⊆ s) :
    comp (ofFun id analyticOnNhd_id) hg = AlgHom.id ℂ (holomorphicGerms s) := by
  refine AlgHom.ext fun k ↦ ?_
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  rw [comp_ofFun]
  rfl

/-- If `spectrum ℂ g ⊆ t` and `spectrum ℂ k ⊆ u`, then `spectrum ℂ (comp g hg k) ⊆ u`. -/
theorem spectrum_comp_subset (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms t) (hk : spectrum ℂ k ⊆ u) :
    spectrum ℂ (comp g hg k) ⊆ u := by
  intro c hc
  rw [spectrum_eq] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  rw [eval_comp]
  exact hk (by rw [spectrum_eq]; exact ⟨eval x hx g, _, rfl⟩)

/-- Pullback of holomorphic germs is functorial under composition. -/
@[simp]
theorem comp_comp (g : holomorphicGerms s) (hg : spectrum ℂ g ⊆ t)
    (k : holomorphicGerms t) (hk : spectrum ℂ k ⊆ u) (m : holomorphicGerms u) :
    comp g hg (comp k hk m) = comp (comp g hg k) (spectrum_comp_subset g hg k hk) m := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofFun_eq k
  obtain ⟨θ, hθ, rfl⟩ := exists_ofFun_eq m
  simp [Function.comp_def]

end TauCeti.holomorphicGerms
