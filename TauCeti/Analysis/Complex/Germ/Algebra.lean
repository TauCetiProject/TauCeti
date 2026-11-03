/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import TauCeti.Order.Filter.Germ

/-!
# Holomorphic germs near a set

`holomorphicGerms s` is the complex subalgebra of `Filter.Germ (𝓝ˢ s) ℂ` represented
by functions holomorphic on an open neighbourhood of `s`. Its elements remember the
function near the whole set, not just its values on that set. This is the domain for
a holomorphic functional calculus near a spectrum, including disconnected spectra.

We construct evaluation and restriction homomorphisms and characterize units by
nonvanishing on `s`. Consequently the spectrum of a represented germ is exactly the
image of `s`, and the coordinate germ has spectrum `s`. No compactness or nonemptiness
is needed; at the empty set the germ algebra is the zero algebra.

The construction uses Mathlib's `AnalyticOnNhd.congr'` for independence of representatives
and `Filter.Germ` for the quotient and its pointwise operations.
-/

public noncomputable section

open Filter Set Topology

namespace TauCeti

/-- Germs along `𝓝ˢ s` represented by functions holomorphic near every point of `s`. -/
def holomorphicGerms (s : Set ℂ) : Subalgebra ℂ (Germ (𝓝ˢ s) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f s ∧ (f : Germ (𝓝ˢ s) ℂ) = g}
  algebraMap_mem' c := ⟨fun _ ↦ c, analyticOnNhd_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, Germ.coe_add f g⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, Germ.coe_mul f g⟩

/-- Membership means admitting a holomorphic representative. -/
theorem mem_holomorphicGerms_iff {s : Set ℂ} {g : Germ (𝓝ˢ s) ℂ} :
    g ∈ holomorphicGerms s ↔
      ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f s ∧ (f : Germ (𝓝ˢ s) ℂ) = g := Iff.rfl

/-- Whether a function represents a holomorphic germ is independent of its representative. -/
@[simp]
theorem coe_mem_holomorphicGerms_iff {s : Set ℂ} {f : ℂ → ℂ} :
    (f : Germ (𝓝ˢ s) ℂ) ∈ holomorphicGerms s ↔ AnalyticOnNhd ℂ f s := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact hg.congr' (Germ.coe_eq.mp hgf)
  · intro hf
    exact ⟨f, hf, rfl⟩

/-- Representatives are holomorphic on an actual open neighbourhood of the set. -/
theorem mem_holomorphicGerms_iff_exists_open {s : Set ℂ} {g : Germ (𝓝ˢ s) ℂ} :
    g ∈ holomorphicGerms s ↔ ∃ (U : Set ℂ) (f : ℂ → ℂ), IsOpen U ∧ s ⊆ U ∧
      DifferentiableOn ℂ f U ∧ (f : Germ (𝓝ˢ s) ℂ) = g := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨{z | AnalyticAt ℂ f z}, f, isOpen_analyticAt ℂ f, hf,
      fun z hz ↦ hz.differentiableAt.differentiableWithinAt, rfl⟩
  · rintro ⟨U, f, hU, hsU, hf, rfl⟩
    exact coe_mem_holomorphicGerms_iff.mpr ((hf.analyticOnNhd hU).mono hsU)

namespace holomorphicGerms

variable {s t : Set ℂ}

/-- A function holomorphic near `s`, as an element of the algebra of germs. -/
def ofFun (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) : holomorphicGerms s :=
  ⟨f, coe_mem_holomorphicGerms_iff.mpr hf⟩

@[simp]
theorem coe_ofFun (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) :
    (ofFun f hf : Germ (𝓝ˢ s) ℂ) = f := (rfl)

/-- Every holomorphic germ has a holomorphic representative. -/
theorem exists_ofFun_eq (g : holomorphicGerms s) :
    ∃ (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s), ofFun f hf = g := by
  obtain ⟨f, hf, hfg⟩ := g.property
  exact ⟨f, hf, Subtype.ext hfg⟩

/-- Two holomorphic representatives define the same germ exactly when they agree near `s`. -/
theorem ofFun_eq_iff {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s)
    (hg : AnalyticOnNhd ℂ g s) : ofFun f hf = ofFun g hg ↔ f =ᶠ[𝓝ˢ s] g := by
  rw [Subtype.ext_iff, coe_ofFun, coe_ofFun, Germ.coe_eq]

@[simp]
theorem ofFun_add (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s)
    (hg : AnalyticOnNhd ℂ g s) : ofFun (f + g) (hf.add hg) = ofFun f hf + ofFun g hg :=
  Subtype.ext (Germ.coe_add f g)

@[simp]
theorem ofFun_mul (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s)
    (hg : AnalyticOnNhd ℂ g s) : ofFun (f * g) (hf.mul hg) = ofFun f hf * ofFun g hg :=
  Subtype.ext (Germ.coe_mul f g)

@[simp]
theorem ofFun_const (c : ℂ) :
    ofFun (fun _ ↦ c) (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ ↦ c) s) =
      algebraMap ℂ (holomorphicGerms s) c := (rfl)

/-- Evaluation of a germ at a point of its base set. -/
noncomputable def eval (x : ℂ) (hx : x ∈ s) : holomorphicGerms s →ₐ[ℂ] ℂ where
  toFun g := Germ.liftOn g.val (fun f ↦ f x)
    (fun _ _ h ↦ h.self_of_nhdsSet hx)
  map_zero' := rfl
  map_one' := rfl
  map_add' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    obtain ⟨k, hk, rfl⟩ := exists_ofFun_eq h
    rfl
  map_mul' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    obtain ⟨k, hk, rfl⟩ := exists_ofFun_eq h
    rfl
  commutes' _ := rfl

@[simp]
theorem eval_ofFun (x : ℂ) (hx : x ∈ s) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) :
    eval x hx (ofFun f hf) = f x := (rfl)

/-- Restriction of a germ near `s` to a subset `t`. -/
def restrict (h : t ⊆ s) : holomorphicGerms s →ₐ[ℂ] holomorphicGerms t where
  toFun g := ⟨Germ.map' id (fun _ _ he ↦ he.filter_mono (nhdsSet_mono h)) g.val, by
    obtain ⟨f, hf, hfg⟩ := g.property
    rw [← hfg]
    -- Mapping a representative by the identity leaves that representative unchanged.
    exact coe_mem_holomorphicGerms_iff.mpr (hf.mono h)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' g k := by
    obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    obtain ⟨k, hk, rfl⟩ := exists_ofFun_eq k
    rfl
  map_mul' g k := by
    obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    obtain ⟨k, hk, rfl⟩ := exists_ofFun_eq k
    rfl
  commutes' _ := rfl

@[simp]
theorem restrict_ofFun (h : t ⊆ s) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) :
    restrict h (ofFun f hf) = ofFun f (hf.mono h) := (rfl)

@[simp]
theorem restrict_refl : restrict (Subset.rfl : s ⊆ s) = AlgHom.id ℂ (holomorphicGerms s) := by
  ext g
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  rfl

/-- Successive restrictions are restriction along the composite inclusion. -/
@[simp]
theorem restrict_comp {u : Set ℂ} (htu : u ⊆ t) (hst : t ⊆ s) :
    (restrict htu).comp (restrict hst) = restrict (htu.trans hst) := by
  ext g
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  rfl

@[simp]
theorem eval_restrict (h : t ⊆ s) (x : ℂ) (hx : x ∈ t) (g : holomorphicGerms s) :
    eval x hx (restrict h g) = eval x (h hx) g := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  rfl

/-- A holomorphic germ is a unit exactly when it is nonzero at every point of the set. -/
theorem isUnit_iff (g : holomorphicGerms s) :
    IsUnit g ↔ ∀ (x : ℂ) (hx : x ∈ s), eval x hx g ≠ 0 := by
  constructor
  · intro hg x hx
    exact isUnit_iff_ne_zero.mp (hg.map (eval x hx).toMonoidHom)
  · obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    intro h
    have hne : ∀ x ∈ s, f x ≠ 0 := by simpa using h
    have hinv : AnalyticOnNhd ℂ (fun z ↦ (f z)⁻¹) s := fun x hx ↦ (hf x hx).inv (hne x hx)
    refine isUnit_iff_exists_inv.mpr ⟨ofFun (fun z ↦ (f z)⁻¹) hinv, ?_⟩
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    filter_upwards [(hf x hx).continuousAt.eventually_ne (hne x hx)] with z hz
    exact mul_inv_cancel₀ hz

/-- The spectrum of a holomorphic germ is its set of values on the base set. -/
theorem spectrum_eq (g : holomorphicGerms s) :
    spectrum ℂ g = {c | ∃ (x : ℂ) (hx : x ∈ s), eval x hx g = c} := by
  ext c
  simp only [spectrum.mem_iff, isUnit_iff, map_sub, AlgHom.commutes,
    Algebra.algebraMap_self, sub_ne_zero, not_forall, not_not]
  exact exists_congr fun x ↦ exists_congr fun hx ↦ eq_comm

/-- The spectrum of a represented holomorphic germ is the image of the base set. -/
theorem spectrum_ofFun (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) :
    spectrum ℂ (ofFun f hf) = f '' s := by
  ext c
  simp [spectrum_eq, Set.mem_image]

/-- The coordinate germ has spectrum exactly the base set, including when the set is empty. -/
@[simp]
theorem spectrum_ofFun_id :
    spectrum ℂ (ofFun id (analyticOnNhd_id : AnalyticOnNhd ℂ id s)) = s := by
  rw [spectrum_ofFun, image_id]

end holomorphicGerms

end TauCeti
