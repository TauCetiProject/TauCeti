/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Rings of analytic function germs

`TauCeti.analyticGerms 𝕜 a` is the subring of function germs at `a` represented by functions
analytic at `a`. Equality is ordinary equality of germs, so restriction to smaller neighborhoods
requires no additional identifications. Analytic maps induce ring homomorphisms by pullback.
These rings allow operations on local analytic functions to be compared independently of the
representatives and neighborhoods used to construct them. The subring construction follows
`TauCeti.meromorphicGerms`, using ordinary neighborhoods and `AnalyticAt` in place of punctured
neighborhoods and `MeromorphicAt`.
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

/-- Pullback of scalar analytic germs along a map analytic at the base point. -/
def pullback (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b) :
    analyticGerms 𝕜 b →+* analyticGerms 𝕜 a where
  toFun φ := ⟨(φ : Germ (𝓝 b) 𝕜).compTendsto g
    (by simpa only [hga] using hg.continuousAt.tendsto), by
    obtain ⟨f, hf, hφ⟩ := φ.2
    rw [← hφ, Germ.coe_compTendsto, coe_mem_analyticGerms]
    exact hf.comp_of_eq hg hga⟩
  map_zero' := Subtype.ext <| Germ.const_compTendsto 0
    (by simpa only [hga] using hg.continuousAt.tendsto)
  map_one' := Subtype.ext <| Germ.const_compTendsto 1
    (by simpa only [hga] using hg.continuousAt.tendsto)
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
      (φ : Germ (𝓝 b) 𝕜).compTendsto g (by simpa only [hga] using hg.continuousAt.tendsto) := (rfl)

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
theorem pullback_id (φ : analyticGerms 𝕜 a) :
    pullback (b := a) id analyticAt_id rfl φ = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt]
  rfl

/-- Pullback depends only on the germ of the analytic map. -/
theorem pullback_congr {g g' : E → F} (hg : AnalyticAt 𝕜 g a) (hg' : AnalyticAt 𝕜 g' a)
    (hga : g a = b) (hg'a : g' a = b) (h : g =ᶠ[𝓝 a] g') :
    pullback g hg hga = pullback g' hg' hg'a := by
  ext φ
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt, coe_ofAnalyticAt,
    coe_ofAnalyticAt, Germ.coe_eq]
  exact h.fun_comp f

/-- Pullbacks compose in the opposite order to analytic maps. -/
@[simp]
theorem pullback_pullback {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (g : E → F) (hg : AnalyticAt 𝕜 g a) (h : F → G) (hh : AnalyticAt 𝕜 h (g a))
    (φ : analyticGerms 𝕜 (h (g a))) :
    pullback g hg rfl (pullback h hh rfl φ) = pullback (h ∘ g) (hh.comp hg) rfl φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt, pullback_ofAnalyticAt]
  rfl

end analyticGerms

end TauCeti
