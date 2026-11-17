/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import TauCeti.Order.Filter.Germ

/-!
# Holomorphic germs near a set

`holomorphicGerms s` is the complex subalgebra of `Filter.Germ (𝓝ˢ s) ℂ` represented
by functions holomorphic on an open neighbourhood of `s`. Its elements remember the
function near the whole set, not just its values on that set. This is the domain for
a holomorphic functional calculus near a spectrum, including disconnected spectra.

We construct evaluation and restriction homomorphisms, the nonunital subalgebra
`holomorphicGerms.vanishingAt` of germs vanishing at a marked point, and characterize units by
nonvanishing on `s`. Consequently the spectrum of a represented germ is exactly the
image of `s`, and the coordinate germ has spectrum `s`. We also record how unital complex-algebra
homomorphisms out of `holomorphicGerms s` act on polynomial and nonvanishing quotient germs.
No compactness or nonemptiness is needed; at the empty set the germ algebra is the zero algebra.

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

/-- The constant function `1` represents the multiplicative identity germ. -/
@[simp]
theorem ofFun_one :
    ofFun (1 : ℂ → ℂ) (analyticOnNhd_const : AnalyticOnNhd ℂ (1 : ℂ → ℂ) s) = 1 := (rfl)

/-- Negation of analytic representatives corresponds to negation of holomorphic germs. -/
@[simp]
theorem ofFun_neg (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) :
    ofFun (-f) hf.neg = -ofFun f hf :=
  Subtype.ext (Germ.coe_neg f)

/-- Differences of analytic representatives correspond to differences of holomorphic germs. -/
@[simp]
theorem ofFun_sub (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s)
    (hg : AnalyticOnNhd ℂ g s) : ofFun (f - g) (hf.sub hg) = ofFun f hf - ofFun g hg :=
  Subtype.ext (Germ.coe_sub f g)

/-- Natural-number powers of analytic representatives correspond to powers of holomorphic germs. -/
@[simp]
theorem ofFun_pow (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) (n : ℕ) :
    ofFun (f ^ n) (hf.pow n) = ofFun f hf ^ n :=
  Subtype.ext (Germ.coe_pow f n)

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

/-- The nonunital complex subalgebra of `holomorphicGerms s` consisting of germs vanishing at a
marked point `x ∈ s`. -/
def vanishingAt (s : Set ℂ) (x : ℂ) (hx : x ∈ s) :
    NonUnitalSubalgebra ℂ (holomorphicGerms s) :=
  NonUnitalAlgHom.equalizer (eval x hx).toNonUnitalAlgHom 0

/-- Membership in `holomorphicGerms.vanishingAt s x hx` means vanishing under `eval x hx`. -/
@[simp]
theorem mem_vanishingAt_iff {s : Set ℂ} {x : ℂ} {hx : x ∈ s} {g : holomorphicGerms s} :
    g ∈ vanishingAt s x hx ↔ eval x hx g = 0 := Iff.rfl

/-- Coercing a germ in `vanishingAt s x hx` to `holomorphicGerms s` gives a germ vanishing at
`x`. -/
@[simp]
theorem eval_coe_vanishingAt {s : Set ℂ} {x : ℂ} {hx : x ∈ s} (g : vanishingAt s x hx) :
    eval x hx (g : holomorphicGerms s) = 0 :=
  mem_vanishingAt_iff.mp g.property

/-- Construct an element of `holomorphicGerms.vanishingAt` from an analytic representative `f`
satisfying `f x = 0`. -/
def ofFunVanishingAt {s : Set ℂ} {x : ℂ} (hx : x ∈ s) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s)
    (hf0 : f x = 0) : vanishingAt s x hx :=
  ⟨ofFun f hf, mem_vanishingAt_iff.mpr (by simpa using hf0)⟩

/-- Coercing `ofFunVanishingAt` back to `holomorphicGerms s` recovers `ofFun f hf`. -/
@[simp]
theorem coe_ofFunVanishingAt {s : Set ℂ} {x : ℂ} (hx : x ∈ s) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f s) (hf0 : f x = 0) :
    (ofFunVanishingAt hx f hf hf0 : holomorphicGerms s) = ofFun f hf := (rfl)

/-- The holomorphic germ of a polynomial function `z ↦ p.eval z` equals `Polynomial.aeval` at the
coordinate germ. -/
theorem ofFun_eval_polynomial (p : Polynomial ℂ) :
    ofFun (fun z => p.eval z) ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)) =
      Polynomial.aeval (ofFun id (analyticOnNhd_id : AnalyticOnNhd ℂ id s)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq, ← ofFun_add, ofFun_eq_iff]
    exact Eventually.of_forall fun z => Polynomial.eval_add
  | monomial n c =>
    rw [Polynomial.aeval_monomial, ← ofFun_const, ← ofFun_pow, ← ofFun_mul, ofFun_eq_iff]
    exact Eventually.of_forall fun z => by simp [Polynomial.eval_monomial]

/-- Any unital complex-algebra homomorphism on `holomorphicGerms s` sending the coordinate germ to
`a` agrees with `Polynomial.aeval a` on polynomial germs. -/
theorem algHom_ofFun_polynomial {A : Type*} [Semiring A] [Algebra ℂ A] {a : A}
    {Φ : holomorphicGerms s →ₐ[ℂ] A}
    (hΦ : Φ (ofFun id analyticOnNhd_id) = a) (p : Polynomial ℂ) :
    Φ (ofFun (fun z => p.eval z) ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))) =
      Polynomial.aeval a p := by
  rw [ofFun_eval_polynomial, ← Polynomial.aeval_algHom_apply, hΦ]

/-- Any unital complex-algebra homomorphism `Φ : holomorphicGerms s →ₐ[ℂ] A` sends a quotient
`f / g` with `g` nonvanishing on `s` to `Φ f * Ring.inverse (Φ g)`. -/
theorem algHom_ofFun_div {A : Type*} [Semiring A] [Algebra ℂ A]
    (Φ : holomorphicGerms s →ₐ[ℂ] A) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s)
    (hg : AnalyticOnNhd ℂ g s) (hg0 : ∀ z ∈ s, g z ≠ 0) :
    Φ (ofFun (fun z => f z / g z) (hf.div hg hg0)) =
      Φ (ofFun f hf) * Ring.inverse (Φ (ofFun g hg)) := by
  have hu : IsUnit (Φ (ofFun g hg)) :=
    ((isUnit_iff _).mpr fun z hz => by simpa using hg0 z hz).map Φ
  have hmul :
      ofFun (fun z => f z / g z) (hf.div hg hg0) * ofFun g hg = ofFun f hf := by
    rw [← ofFun_mul, ofFun_eq_iff]
    refine eventually_nhdsSet_iff_forall.mpr fun z hz => ?_
    filter_upwards [(hg z hz).continuousAt.eventually_ne (hg0 z hz)] with x hx
    exact div_mul_cancel₀ (f x) hx
  have hΦmul := congrArg Φ hmul
  rw [map_mul] at hΦmul
  rw [← hΦmul, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]

end holomorphicGerms

end TauCeti
