/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Rings of analytic function germs

`TauCeti.analyticGerms 𝕜 a` is the subring of function germs at `a` represented by functions
analytic at `a`. Equality is ordinary equality of germs, so restriction to smaller neighborhoods
requires no additional identifications. Analytic maps induce ring homomorphisms by pullback.
These rings allow operations on local analytic functions to be compared independently of the
representatives and neighborhoods used to construct them. Locally inverse analytic maps give
ring equivalences (`TauCeti.analyticGerms.equivOfInverse`), without choosing representatives.
The subring construction follows `TauCeti.meromorphicGerms`, using ordinary neighborhoods and
`AnalyticAt` in place of punctured neighborhoods and `MeromorphicAt`. The local-inverse
construction is analogous to `OpenPartialHomeomorph.meromorphicGermsEquiv`.

Over `ℝ` or `ℂ` the ring of analytic germs is an integral domain
(`TauCeti.analyticGerms.instIsDomain`): if a product of analytic functions vanishes near a point,
then one of the factors does (`AnalyticAt.mul_eventuallyEq_zero_iff`), by the identity theorem on
a ball around that point.
-/

public section

open Filter Topology

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The ring of scalar analytic germs at `a`, inside the ring of all function germs. -/
def analyticGerms (a : E) : Subring (Germ (𝓝 a) 𝕜) where
  carrier := {φ | ∃ f : E → 𝕜, AnalyticAt 𝕜 f a ∧ (f : Germ (𝓝 a) 𝕜) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

variable {𝕜} {a : E} {b : F}

/-- Membership in the analytic germ ring means having an analytic representative. -/
theorem mem_analyticGerms_iff {φ : Germ (𝓝 a) 𝕜} :
    φ ∈ analyticGerms 𝕜 a ↔ ∃ f : E → 𝕜, AnalyticAt 𝕜 f a ∧ (f : Germ (𝓝 a) 𝕜) = φ :=
  Iff.rfl

/-- A function has an analytic germ exactly when it is analytic at the base point. -/
@[simp]
theorem coe_mem_analyticGerms {f : E → 𝕜} :
    (f : Germ (𝓝 a) 𝕜) ∈ analyticGerms 𝕜 a ↔ AnalyticAt 𝕜 f a :=
  ⟨fun ⟨_, hg, hgf⟩ ↦ hg.congr (Germ.coe_eq.1 hgf), fun hf ↦ ⟨f, hf, rfl⟩⟩

namespace analyticGerms

/-- The germ of a function analytic at the base point. -/
def ofAnalyticAt (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a) : analyticGerms 𝕜 a :=
  ⟨f, coe_mem_analyticGerms.2 hf⟩

@[simp]
theorem coe_ofAnalyticAt (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a) :
    ((ofAnalyticAt f hf : analyticGerms 𝕜 a) : Germ (𝓝 a) 𝕜) = f := (rfl)

/-- The zero function represents the zero analytic germ. -/
@[simp]
theorem ofAnalyticAt_zero :
    ofAnalyticAt (0 : E → 𝕜) (a := a) analyticAt_const = 0 := (rfl)

/-- The constant one function represents the unit analytic germ. -/
@[simp]
theorem ofAnalyticAt_one :
    ofAnalyticAt (1 : E → 𝕜) (a := a) analyticAt_const = 1 := (rfl)

/-- Taking analytic germs preserves addition. -/
@[simp]
theorem ofAnalyticAt_add (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f a)
    (hg : AnalyticAt 𝕜 g a) :
    ofAnalyticAt (f + g) (hf.add hg) = ofAnalyticAt f hf + ofAnalyticAt g hg := (rfl)

/-- Taking analytic germs preserves multiplication. -/
@[simp]
theorem ofAnalyticAt_mul (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f a)
    (hg : AnalyticAt 𝕜 g a) :
    ofAnalyticAt (f * g) (hf.mul hg) = ofAnalyticAt f hf * ofAnalyticAt g hg := (rfl)

/-- Taking analytic germs preserves negation. -/
@[simp]
theorem ofAnalyticAt_neg (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a) :
    ofAnalyticAt (-f) hf.neg = -ofAnalyticAt f hf := (rfl)

/-- Taking analytic germs preserves subtraction. -/
@[simp]
theorem ofAnalyticAt_sub (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f a)
    (hg : AnalyticAt 𝕜 g a) :
    ofAnalyticAt (f - g) (hf.sub hg) = ofAnalyticAt f hf - ofAnalyticAt g hg := (rfl)

/-- Two analytic representatives define the same germ exactly when they agree near the base
point. -/
@[simp]
theorem ofAnalyticAt_eq_ofAnalyticAt_iff {f g : E → 𝕜}
    {hf : AnalyticAt 𝕜 f a} {hg : AnalyticAt 𝕜 g a} :
    ofAnalyticAt f hf = ofAnalyticAt g hg ↔ f =ᶠ[𝓝 a] g := by
  rw [Subtype.ext_iff, coe_ofAnalyticAt, coe_ofAnalyticAt, Germ.coe_eq]

/-- Eventually equal analytic functions represent the same analytic germ. -/
theorem ofAnalyticAt_congr {f g : E → 𝕜} {hf : AnalyticAt 𝕜 f a}
    {hg : AnalyticAt 𝕜 g a} (h : f =ᶠ[𝓝 a] g) :
    ofAnalyticAt f hf = ofAnalyticAt g hg :=
  ofAnalyticAt_eq_ofAnalyticAt_iff.2 h

/-- Pullback of scalar analytic germs along a map analytic at the base point. -/
def pullback (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b) :
    analyticGerms 𝕜 b →+* analyticGerms 𝕜 a where
  toFun φ := ⟨(φ : Germ (𝓝 b) 𝕜).compTendsto g (hga ▸ hg.continuousAt.tendsto), by
    obtain ⟨f, hf, hφ⟩ := φ.2
    rw [← hφ, Germ.coe_compTendsto, coe_mem_analyticGerms]
    exact hf.comp_of_eq hg hga⟩
  map_zero' := Subtype.ext <| Germ.const_compTendsto 0 (hga ▸ hg.continuousAt.tendsto)
  map_one' := Subtype.ext <| Germ.const_compTendsto 1 (hga ▸ hg.continuousAt.tendsto)
  map_add' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := φ.2
    obtain ⟨g, hg, hψ⟩ := ψ.2
    apply Subtype.ext
    simp only [Subring.coe_add, ← hφ, ← hψ, ← Germ.coe_add, Germ.coe_compTendsto]
    rfl
  map_mul' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := φ.2
    obtain ⟨g, hg, hψ⟩ := ψ.2
    apply Subtype.ext
    simp only [Subring.coe_mul, ← hφ, ← hψ, ← Germ.coe_mul, Germ.coe_compTendsto]
    rfl

@[simp]
theorem coe_pullback (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (φ : analyticGerms 𝕜 b) :
    ((pullback g hg hga φ : analyticGerms 𝕜 a) : Germ (𝓝 a) 𝕜) =
      (φ : Germ (𝓝 b) 𝕜).compTendsto g (hga ▸ hg.continuousAt.tendsto) := (rfl)

/-- Pullback sends the germ of `f` to the germ of its composition. -/
@[simp]
theorem pullback_ofAnalyticAt (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (f : F → 𝕜) (hf : AnalyticAt 𝕜 f b) :
    pullback g hg hga (ofAnalyticAt f hf) = ofAnalyticAt (f ∘ g) (hf.comp_of_eq hg hga) :=
  Subtype.ext (by rw [coe_pullback, coe_ofAnalyticAt, coe_ofAnalyticAt,
    Germ.coe_compTendsto])

/-- Every analytic germ is the germ of an analytic function. -/
theorem exists_ofAnalyticAt (φ : analyticGerms 𝕜 a) :
    ∃ (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a), ofAnalyticAt f hf = φ := by
  obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.2
  exact ⟨f, hf, Subtype.ext (by rw [coe_ofAnalyticAt, hφ])⟩

/-- Pullback along the identity fixes each analytic germ. -/
@[simp]
theorem pullback_id (φ : analyticGerms 𝕜 a) (h : id a = a) :
    pullback (b := a) id analyticAt_id h φ = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt]
  rfl

/-- Pullback depends only on the germ of the analytic map. -/
theorem pullback_congr {g g' : E → F} (hg : AnalyticAt 𝕜 g a) (hg' : AnalyticAt 𝕜 g' a)
    (hga : g a = b) (hg'a : g' a = b) (h : g =ᶠ[𝓝 a] g') :
    pullback g hg hga = pullback g' hg' hg'a := by
  apply RingHom.ext
  intro φ
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt]
  exact ofAnalyticAt_congr (h.fun_comp f)

/-- Pullbacks compose in the opposite order to analytic maps. -/
@[simp]
theorem pullback_pullback {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {c : G} (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (h : F → G) (hh : AnalyticAt 𝕜 h b) (hhb : h b = c) (φ : analyticGerms 𝕜 c) :
    pullback g hg hga (pullback h hh hhb φ) =
      pullback (h ∘ g) (hh.comp_of_eq hg hga) (by rw [Function.comp_apply, hga, hhb]) φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt, pullback_ofAnalyticAt]
  rfl

/-- Locally inverse analytic maps identify the scalar analytic germ rings at corresponding
points, contravariantly. Only inverse identities near the two base points are required. -/
def equivOfInverse (g : E → F) (h : F → E)
    (hg : AnalyticAt 𝕜 g a) (hh : AnalyticAt 𝕜 h b) (hga : g a = b)
    (hleft : h ∘ g =ᶠ[𝓝 a] id) (hright : g ∘ h =ᶠ[𝓝 b] id) :
    analyticGerms 𝕜 b ≃+* analyticGerms 𝕜 a where
  toFun := pullback g hg hga
  invFun := pullback h hh (hga ▸ hleft.self_of_nhds)
  map_mul' := map_mul (pullback g hg hga)
  map_add' := map_add (pullback g hg hga)
  left_inv φ := by
    obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
    rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt]
    exact ofAnalyticAt_congr (hright.fun_comp f)
  right_inv φ := by
    obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
    rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt]
    exact ofAnalyticAt_congr (hleft.fun_comp f)

/-- Transport by locally inverse analytic maps is analytic pullback. -/
@[simp]
theorem equivOfInverse_apply (g : E → F) (h : F → E)
    (hg : AnalyticAt 𝕜 g a) (hh : AnalyticAt 𝕜 h b) (hga : g a = b)
    (hleft : h ∘ g =ᶠ[𝓝 a] id) (hright : g ∘ h =ᶠ[𝓝 b] id)
    (φ : analyticGerms 𝕜 b) :
    equivOfInverse g h hg hh hga hleft hright φ = pullback g hg hga φ := (rfl)

/-- Inverse transport is pullback by the local inverse. -/
@[simp]
theorem equivOfInverse_symm_apply (g : E → F) (h : F → E)
    (hg : AnalyticAt 𝕜 g a) (hh : AnalyticAt 𝕜 h b) (hga : g a = b)
    (hleft : h ∘ g =ᶠ[𝓝 a] id) (hright : g ∘ h =ᶠ[𝓝 b] id)
    (φ : analyticGerms 𝕜 a) :
    (equivOfInverse g h hg hh hga hleft hright).symm φ =
      pullback h hh (hga ▸ hleft.self_of_nhds) φ := (rfl)

end analyticGerms

end TauCeti

/-! ### Analytic germs form an integral domain -/

section Domain

open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : E → 𝕜} {a : E}

/-- A product of analytic functions vanishes near a point exactly when one of the factors does.
If the first factor is nonzero at some point of a ball on which both are analytic and the product
vanishes, the second factor vanishes near that point, hence on the whole ball by the identity
theorem. -/
theorem AnalyticAt.mul_eventuallyEq_zero_iff (hf : AnalyticAt 𝕜 f a) (hg : AnalyticAt 𝕜 g a) :
    f * g =ᶠ[𝓝 a] 0 ↔ f =ᶠ[𝓝 a] 0 ∨ g =ᶠ[𝓝 a] 0 := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hf0 ↦ ?_, ?_⟩
  · let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
      ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and h)
    obtain ⟨z, hz, hfz⟩ : ∃ z ∈ Metric.ball a r, f z ≠ 0 := by
      by_contra! H
      exact hf0 (eventually_of_mem (Metric.ball_mem_nhds a hr) H)
    have hgz : g =ᶠ[𝓝 z] 0 := by
      filter_upwards [(hball z hz).1.1.continuousAt.eventually_ne hfz,
        Metric.isOpen_ball.mem_nhds hz] with y hy hyb
      simpa [hy] using (hball y hyb).2
    exact eventually_of_mem (Metric.ball_mem_nhds a hr)
      (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun y hy ↦ (hball y hy).1.2) Metric.isPreconnected_ball hz hgz)
  · rintro (h | h) <;> filter_upwards [h] with y hy <;> simp [hy]

namespace TauCeti.analyticGerms

instance : NoZeroDivisors (analyticGerms 𝕜 a) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
    obtain ⟨g, hg, rfl⟩ := exists_ofAnalyticAt ψ
    have h' : ((f * g : E → 𝕜) : Germ (𝓝 a) 𝕜) = ((0 : E → 𝕜) : Germ (𝓝 a) 𝕜) :=
      congrArg Subtype.val h
    refine ((hf.mul_eventuallyEq_zero_iff hg).1 (Germ.coe_eq.1 h')).imp
      (fun h0 ↦ Subtype.ext (Germ.coe_eq.2 h0)) (fun h0 ↦ Subtype.ext (Germ.coe_eq.2 h0))

/-- Over `ℝ` or `ℂ`, analytic germs at a point form an integral domain. -/
instance instIsDomain : IsDomain (analyticGerms 𝕜 a) :=
  NoZeroDivisors.to_isDomain _

end TauCeti.analyticGerms

end Domain
