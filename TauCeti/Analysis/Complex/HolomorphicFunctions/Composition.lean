/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ

/-!
# Composition of holomorphic functions and germs

For `f : holomorphicFunctions U` mapping `U` into an open set `V`, precomposition `g ↦ g ∘ f`
defines a continuous complex-algebra homomorphism `HolomorphicFunctions.compAlgHom` from
`holomorphicFunctions V` to `holomorphicFunctions U` for the compact-open topology. More generally,
whenever `f` maps a subset `s ⊆ U` into `V`, the preimage `HolomorphicFunctions.pullbackOpens f V`
is an open neighbourhood `U' ≤ U` of `s` on which `f` takes values in `V`.

Descending along restriction to germs gives `holomorphicGerms.compAlgHom`: if a germ
`φ : holomorphicGerms s` maps every point of `s` into `t`, precomposition with `φ` is a unital
complex-algebra homomorphism `holomorphicGerms t →ₐ[ℂ] holomorphicGerms s` sending the coordinate
germ on `t` to `φ` and intertwining point evaluation.

## Main definitions

* `TauCeti.HolomorphicFunctions.pullbackOpens`: the open subset of `U` mapped by `f` into `V`.
* `TauCeti.HolomorphicFunctions.compAlgHom`: precomposition `holomorphicFunctions V →ₐ[ℂ]
  holomorphicFunctions U` along `f : holomorphicFunctions U` mapping `U` into `V`.
* `TauCeti.holomorphicGerms.compAlgHom`: precomposition `holomorphicGerms t →ₐ[ℂ]
  holomorphicGerms s` along `φ : holomorphicGerms s` mapping `s` into `t`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Filter Set TopologicalSpace Topology

namespace TauCeti

namespace HolomorphicFunctions

variable {U V W : Opens ℂ}

/-- The open subset of `U` consisting of points mapped by `f : holomorphicFunctions U` into `V`. -/
def pullbackOpens (f : holomorphicFunctions U) (V : Opens ℂ) : Opens ℂ :=
  ⟨Subtype.val '' (f.val ⁻¹' (V : Set ℂ)),
    U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage f.val.continuous)⟩

@[simp]
theorem mem_pullbackOpens {f : holomorphicFunctions U} {V : Opens ℂ} {z : ℂ} :
    z ∈ pullbackOpens f V ↔ ∃ hz : z ∈ U, f.val ⟨z, hz⟩ ∈ V := by
  simp only [pullbackOpens, Opens.mem_mk, mem_image, mem_preimage, Subtype.exists]
  exact ⟨fun ⟨w, hwU, hwV, hzw⟩ => ⟨hzw ▸ hwU, hzw ▸ hwV⟩, fun ⟨hz, hzV⟩ => ⟨z, hz, hzV, rfl⟩⟩

theorem pullbackOpens_le (f : holomorphicFunctions U) (V : Opens ℂ) :
    pullbackOpens f V ≤ U := by
  intro z hz
  exact (mem_pullbackOpens.mp hz).1

theorem pullbackOpens_mono {V₁ V₂ : Opens ℂ} (f : holomorphicFunctions U) (hV : V₁ ≤ V₂) :
    pullbackOpens f V₁ ≤ pullbackOpens f V₂ := by
  intro z hz
  obtain ⟨hzU, hzV⟩ := mem_pullbackOpens.mp hz
  exact mem_pullbackOpens.mpr ⟨hzU, hV hzV⟩

theorem subset_pullbackOpens {s : Set ℂ} {f : holomorphicFunctions U} {V : Opens ℂ}
    (hsU : s ⊆ U) (hf : ∀ x (hx : x ∈ s), f.val ⟨x, hsU hx⟩ ∈ V) :
    s ⊆ pullbackOpens f V := fun x hx =>
  mem_pullbackOpens.mpr ⟨hsU hx, hf x hx⟩

theorem apply_mem_of_mem_pullbackOpens (f : holomorphicFunctions U) (V : Opens ℂ)
    (z : pullbackOpens f V) :
    (restrict (pullbackOpens_le f V) f).val z ∈ V := by
  obtain ⟨_, hzV⟩ := mem_pullbackOpens.mp z.property
  rwa [restrict_apply]

theorem mapsTo_extend_pullbackOpens (f : holomorphicFunctions U) (V : Opens ℂ) :
    MapsTo (extend f) (pullbackOpens f V : Set ℂ) V := by
  intro z hz
  obtain ⟨hzU, hzV⟩ := mem_pullbackOpens.mp hz
  rwa [extend_apply f ⟨z, hzU⟩]

/-- If `f : holomorphicFunctions U` maps a subset `s ⊆ U` into an open set `V`, there is a smaller
open neighbourhood `U' ≤ U` of `s` on which `f` maps into `V`. -/
theorem exists_opens_mapsTo {s : Set ℂ} (hsU : s ⊆ U) (f : holomorphicFunctions U) (V : Opens ℂ)
    (hf : ∀ x (hx : x ∈ s), f.val ⟨x, hsU hx⟩ ∈ V) :
    ∃ (U' : Opens ℂ) (_ : s ⊆ U') (hU'U : U' ≤ U),
      ∀ z : U', (restrict hU'U f).val z ∈ V :=
  ⟨pullbackOpens f V, subset_pullbackOpens hsU hf, pullbackOpens_le f V,
    apply_mem_of_mem_pullbackOpens f V⟩

/-- Precomposition of holomorphic functions on `V` with a holomorphic map
`f : holomorphicFunctions U` taking values in `V`. -/
def compAlgHom (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ
    (⟨fun z => ⟨f.val z, hf z⟩, f.val.continuous.subtype_mk hf⟩ : C(U, V))).comp
    (holomorphicFunctions V).val).codRestrict (holomorphicFunctions U) fun g =>
      (mem_holomorphicFunctions_iff_of_eqOn (g := extend g ∘ extend f) fun z => by
        simp only [Function.comp_apply, extend_apply f z]
        exact extend_apply g ⟨f.val z, hf z⟩).mpr <|
        (differentiableOn_extend g).comp (differentiableOn_extend f) fun z hz => by
          rw [extend_apply f ⟨z, hz⟩]
          exact hf ⟨z, hz⟩

@[simp]
theorem compAlgHom_apply (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V)
    (g : holomorphicFunctions V) (z : U) :
    (compAlgHom f hf g).val z = g.val ⟨f.val z, hf z⟩ := (rfl)

/-- `extend` on `U` intertwines `compAlgHom` with composition of extended functions. -/
theorem extend_compAlgHom_apply (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V)
    (g : holomorphicFunctions V) (z : U) :
    extend (compAlgHom f hf g) z = extend g (f.val z) := by
  rw [extend_apply, compAlgHom_apply, ← extend_apply g ⟨f.val z, hf z⟩]

@[simp]
theorem compAlgHom_of (f : ℂ → ℂ) (hfU : DifferentiableOn ℂ f U) (hfV : MapsTo f U V)
    (g : ℂ → ℂ) (hgV : DifferentiableOn ℂ g V) :
    compAlgHom (of U f hfU) (fun z => by rw [of_apply]; exact hfV z.property) (of V g hgV) =
      of U (g ∘ f) (hgV.comp hfU hfV) := by
  apply Subtype.ext
  ext z
  simp

@[simp]
theorem compAlgHom_id (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    compAlgHom f hf (of V id differentiableOn_id) = f := by
  apply Subtype.ext
  ext z
  simp

@[simp]
theorem restrict_compAlgHom (hWU : W ≤ U) (f : holomorphicFunctions U)
    (hf : ∀ z : U, f.val z ∈ V) (g : holomorphicFunctions V) :
    restrict hWU (compAlgHom f hf g) =
      compAlgHom (restrict hWU f) (fun z => by rw [restrict_apply]; exact hf (Set.inclusion hWU z))
        g := by
  apply Subtype.ext
  ext z
  simp

@[simp]
theorem compAlgHom_restrict {V' : Opens ℂ} (hVV' : V ≤ V') (f : holomorphicFunctions U)
    (hf : ∀ z : U, f.val z ∈ V) (g : holomorphicFunctions V') :
    compAlgHom f hf (restrict hVV' g) = compAlgHom f (fun z => hVV' (hf z)) g := by
  apply Subtype.ext
  ext z
  simp

/-- Precomposition along a holomorphic map is continuous for the compact-open topology. -/
@[continuity]
theorem continuous_compAlgHom (f : holomorphicFunctions U) (hf : ∀ z : U, f.val z ∈ V) :
    Continuous (compAlgHom f hf) := by
  unfold compAlgHom
  exact ((ContinuousMap.compRightAlgHom_continuous ℂ ℂ
    (⟨fun z => ⟨f.val z, hf z⟩, f.val.continuous.subtype_mk hf⟩ : C(U, V))).comp
    continuous_subtype_val).subtype_mk _

end HolomorphicFunctions

namespace holomorphicGerms

open HolomorphicFunctions

variable {s t : Set ℂ}

section Comp

private def compRepOpen (φ : holomorphicGerms s) : Opens ℂ :=
  (exists_toGerm_eq φ).choose

private theorem subset_compRepOpen (φ : holomorphicGerms s) : s ⊆ compRepOpen φ :=
  (exists_toGerm_eq φ).choose_spec.choose

private def compRepFun (φ : holomorphicGerms s) : holomorphicFunctions (compRepOpen φ) :=
  (exists_toGerm_eq φ).choose_spec.choose_spec.choose

private theorem toGerm_compRepFun (φ : holomorphicGerms s) :
    toGerm (subset_compRepOpen φ) (compRepFun φ) = φ :=
  (exists_toGerm_eq φ).choose_spec.choose_spec.choose_spec

private theorem subset_pullbackOpens_compRepFun {φ : holomorphicGerms s}
    (hφ : ∀ (x : ℂ) (hx : x ∈ s), eval x hx φ ∈ t) (V : Opens ℂ) (htV : t ⊆ V) :
    s ⊆ pullbackOpens (compRepFun φ) V :=
  subset_pullbackOpens (subset_compRepOpen φ) fun x hx => by
    rw [← eval_toGerm (subset_compRepOpen φ) x hx, toGerm_compRepFun]
    exact htV (hφ x hx)

/-- Precomposition of holomorphic germs near `t` with a holomorphic germ `φ` near `s` whose point
values on `s` lie in `t`. -/
def compAlgHom (φ : holomorphicGerms s) (hφ : ∀ (x : ℂ) (hx : x ∈ s), eval x hx φ ∈ t) :
    holomorphicGerms t →ₐ[ℂ] holomorphicGerms s :=
  lift
    (fun V htV =>
      (toGerm (subset_pullbackOpens_compRepFun hφ V htV)).comp
        (HolomorphicFunctions.compAlgHom
          (HolomorphicFunctions.restrict (pullbackOpens_le (compRepFun φ) V) (compRepFun φ))
          (apply_mem_of_mem_pullbackOpens (compRepFun φ) V)))
    fun U V htV hVU f => by
      simp only [AlgHom.comp_apply]
      have hle : pullbackOpens (compRepFun φ) V ≤ pullbackOpens (compRepFun φ) U :=
        pullbackOpens_mono (compRepFun φ) hVU
      rw [← toGerm_restrict (subset_pullbackOpens_compRepFun hφ V htV) hle]
      congr 1
      apply Subtype.ext
      ext z
      simp

/-- Precomposition of a function germ with a represented germ agrees with composing on any smaller
open neighbourhood `U'` of `s` mapped into `V`. -/
theorem compAlgHom_toGerm {U V U' : Opens ℂ} (φ : holomorphicGerms s)
    (hφ : ∀ (x : ℂ) (hx : x ∈ s), eval x hx φ ∈ t) (hsU : s ⊆ U) (f : holomorphicFunctions U)
    (hfφ : toGerm hsU f = φ) (htV : t ⊆ V) (g : holomorphicFunctions V)
    (hsU' : s ⊆ U') (hU'U : U' ≤ U)
    (hfV : ∀ z : U', (HolomorphicFunctions.restrict hU'U f).val z ∈ V) :
    compAlgHom φ hφ (toGerm htV g) =
      toGerm hsU'
        (HolomorphicFunctions.compAlgHom (HolomorphicFunctions.restrict hU'U f) hfV g) := by
  rw [compAlgHom, lift_toGerm, AlgHom.comp_apply]
  obtain ⟨W, hsW, hW₀, hWU, heq⟩ :=
    (toGerm_eq_iff (subset_compRepOpen φ) hsU (compRepFun φ) f).mp
      ((toGerm_compRepFun φ).trans hfφ.symm)
  set P := pullbackOpens (compRepFun φ) V
  have hsP : s ⊆ P := subset_pullbackOpens_compRepFun hφ V htV
  let W' : Opens ℂ := W ⊓ P ⊓ U'
  have hsW' : s ⊆ W' := fun x hx => ⟨⟨hsW hx, hsP hx⟩, hsU' hx⟩
  have hW'P : W' ≤ P := fun _ hz => hz.1.2
  have hW'U' : W' ≤ U' := fun _ hz => hz.2
  refine (toGerm_eq_iff hsP hsU' _ _).mpr ⟨W', hsW', hW'P, hW'U', ?_⟩
  apply Subtype.ext
  ext z
  simp only [HolomorphicFunctions.restrict_apply, HolomorphicFunctions.compAlgHom_apply]
  congr 1
  apply Subtype.ext
  have hzW := congrArg (fun k : holomorphicFunctions W => k.val ⟨z, z.property.1.1⟩) heq
  simpa only [HolomorphicFunctions.restrict_apply] using hzW

@[simp]
theorem compAlgHom_ofFun (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) (hft : MapsTo f s t)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g t) :
    compAlgHom (ofFun f hf) (fun x hx => by simpa using hft hx) (ofFun g hg) =
      ofFun (g ∘ f) (hg.comp hf hft) := by
  let U : Opens ℂ := ⟨{z | AnalyticAt ℂ f z}, isOpen_analyticAt ℂ f⟩
  let V : Opens ℂ := ⟨{z | AnalyticAt ℂ g z}, isOpen_analyticAt ℂ g⟩
  have hfU : DifferentiableOn ℂ f U := fun _ hz => hz.differentiableAt.differentiableWithinAt
  have hgV : DifferentiableOn ℂ g V := fun _ hz => hz.differentiableAt.differentiableWithinAt
  have hsU : s ⊆ U := hf
  have htV : t ⊆ V := hg
  let fH := of U f hfU
  let U' := pullbackOpens fH V
  have hsU' : s ⊆ U' := subset_pullbackOpens hsU fun x hx => by
    rw [of_apply]
    exact htV (hft hx)
  have hU'U : U' ≤ U := pullbackOpens_le fH V
  have hfV : ∀ z : U', (HolomorphicFunctions.restrict hU'U fH).val z ∈ V :=
    apply_mem_of_mem_pullbackOpens fH V
  have hfg := compAlgHom_toGerm (ofFun f hf) (fun x hx => by simpa using hft hx) hsU fH
    (toGerm_of hsU f hfU) htV (of V g hgV) hsU' hU'U hfV
  rw [toGerm_of htV g hgV] at hfg
  refine hfg.trans ?_
  exact toGerm_eq_ofFun hsU' _ (g ∘ f) (hg.comp hf hft) fun z => by
    simp [fH]

/-- Precomposing the coordinate germ on `t` with `φ` recovers `φ`. -/
@[simp]
theorem compAlgHom_id (φ : holomorphicGerms s)
    (hφ : ∀ (x : ℂ) (hx : x ∈ s), eval x hx φ ∈ t) :
    compAlgHom φ hφ (ofFun id analyticOnNhd_id) = φ := by
  obtain ⟨U, hsU, f, rfl⟩ := exists_toGerm_eq φ
  rw [← toGerm_of (U := ⊤) (subset_univ t) id differentiableOn_id,
    compAlgHom_toGerm _ hφ hsU f rfl (subset_univ t) _ hsU (le_refl U) (fun _ => trivial)]
  simp

/-- Point evaluation intertwines germ composition with evaluation at the image point. -/
@[simp]
theorem eval_compAlgHom (φ : holomorphicGerms s)
    (hφ : ∀ (x : ℂ) (hx : x ∈ s), eval x hx φ ∈ t) (ψ : holomorphicGerms t)
    (x : ℂ) (hx : x ∈ s) :
    eval x hx (compAlgHom φ hφ ψ) = eval (eval x hx φ) (hφ x hx) ψ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq φ
  obtain ⟨g, hg, rfl⟩ := exists_ofFun_eq ψ
  have hft : MapsTo f s t := fun z hz => by simpa using hφ z hz
  rw [compAlgHom_ofFun f hf hft g hg]
  simp

@[simp]
theorem compAlgHom_restrict {t' : Set ℂ} (htt' : t ⊆ t') (φ : holomorphicGerms s)
    (hφ : ∀ (x : ℂ) (hx : x ∈ s), eval x hx φ ∈ t) (ψ : holomorphicGerms t') :
    compAlgHom φ hφ (restrict htt' ψ) = compAlgHom φ (fun x hx => htt' (hφ x hx)) ψ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq φ
  obtain ⟨g, hg, rfl⟩ := exists_ofFun_eq ψ
  have hft : MapsTo f s t := fun z hz => by simpa using hφ z hz
  rw [restrict_ofFun, compAlgHom_ofFun f hf hft g (hg.mono htt'),
    compAlgHom_ofFun f hf (hft.mono_right htt') g hg]

end Comp

end holomorphicGerms

end TauCeti
