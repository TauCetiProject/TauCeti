/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Plus
public import Mathlib.Topology.Homeomorph.Defs

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Invariance of completed tensor products under epimorphic base change

Let `φ : A →+* A'` be a homomorphism of topological rings through which the structure maps of two
adic `A'`-algebras `B` and `C` factor (`(algebraMap A' B).comp φ = algebraMap A B` and
`(algebraMap A' C).comp φ = algebraMap A C`). Whenever continuous ring homomorphisms from `A'` into
`B ⊗̂_A C` are determined by their restriction along `φ` — as holds in particular when `φ` is the
canonical map from `A` to a completed rational localisation `A⟨T_A/s_A⟩`, since `B ⊗̂_A C` is
Hausdorff — the canonical map `B ⊗̂_A C →+* B ⊗̂_{A'} C` is a homeomorphic ring isomorphism, and
carries the completed tensor plus ring `(PB.completedTensor A PC).plus` onto
`(PB.completedTensor A' PC).plus`.

Neither completeness, separatedness, nor sheafiness is assumed on `A`, `A'`, `B`, or `C`, and all
four rings live in independent universes.

## Main definitions and results

* `TauCeti.Huber.CompletedTensor.epimorphismBaseEquiv`: the topological ring equivalence
  `B ⊗̂_A C ≃+* B ⊗̂_{A'} C`.
* `TauCeti.Huber.CompletedTensor.isHomeomorph_epimorphismBaseEquiv`: `epimorphismBaseEquiv` is a
  homeomorphism.
* `TauCeti.Huber.Pair.completedTensor.epimorphismBaseEquiv_mem_plus_iff` and
  `TauCeti.Huber.Pair.completedTensor.map_epimorphismBaseEquiv_plus`: `epimorphismBaseEquiv`
  identifies the completed tensor plus rings over `A` and `A'`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2, Proposition
  1.2.2.
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber

universe v w

namespace CompletedTensor

section EpimorphismBase

variable {A : Type*} {A' : Type*} (B : Type v) (C : Type w)
  [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra A' B] [Algebra A' C]
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing A'] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A' B)] [IsAdicHom (algebraMap A' C)]
  (φ : A →+* A')
  (hB : (algebraMap A' B).comp φ = algebraMap A B)
  (hC : (algebraMap A' C).comp φ = algebraMap A C)

private noncomputable def epimorphismBaseTo :
    CompletedTensor A B C →+* CompletedTensor A' B C :=
  lift (inl A' B C) (inr A' B C)
    (by rw [← hB, ← RingHom.comp_assoc, inl_comp_algebraMap, RingHom.comp_assoc, hC])
    (continuous_inl A' B C) (continuous_inr A' B C)

private noncomputable def epimorphismBaseInv
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) :
    CompletedTensor A' B C →+* CompletedTensor A B C :=
  lift (inl A B C) (inr A B C)
    (hepi _ _
      ((continuous_inl A B C).comp (IsAdicHom.continuous inferInstance))
      ((continuous_inr A B C).comp (IsAdicHom.continuous inferInstance))
      (by rw [RingHom.comp_assoc, hB, RingHom.comp_assoc, hC, inl_comp_algebraMap]))
    (continuous_inl A B C) (continuous_inr A B C)

/-- **Base-ring invariance of completed tensor products.** If continuous ring homomorphisms from
`A'` into `B ⊗̂_A C` are determined by their restriction along `φ : A →+* A'`, then
`B ⊗̂_A C ≃+* B ⊗̂_{A'} C` as topological rings. -/
noncomputable def epimorphismBaseEquiv
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) :
    CompletedTensor A B C ≃+* CompletedTensor A' B C :=
  RingEquiv.ofRingHom (epimorphismBaseTo B C φ hB hC) (epimorphismBaseInv B C φ hB hC hepi)
    (hom_ext
      ((continuous_lift _ _ _ _ _).comp (continuous_lift _ _ _ _ _)) continuous_id
      (by ext b; simp [epimorphismBaseTo, epimorphismBaseInv])
      (by ext c; simp [epimorphismBaseTo, epimorphismBaseInv]))
    (hom_ext
      ((continuous_lift _ _ _ _ _).comp (continuous_lift _ _ _ _ _)) continuous_id
      (by ext b; simp [epimorphismBaseTo, epimorphismBaseInv])
      (by ext c; simp [epimorphismBaseTo, epimorphismBaseInv]))

/-- `epimorphismBaseEquiv` is continuous. -/
@[fun_prop]
theorem continuous_epimorphismBaseEquiv
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) :
    Continuous (epimorphismBaseEquiv B C φ hB hC hepi) :=
  continuous_lift _ _ _ _ _

/-- `(epimorphismBaseEquiv …).symm` is continuous. -/
@[fun_prop]
theorem continuous_epimorphismBaseEquiv_symm
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) :
    Continuous (epimorphismBaseEquiv B C φ hB hC hepi).symm :=
  continuous_lift _ _ _ _ _

/-- `epimorphismBaseEquiv` is a homeomorphism. -/
theorem isHomeomorph_epimorphismBaseEquiv
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) :
    IsHomeomorph (epimorphismBaseEquiv B C φ hB hC hepi) :=
  (epimorphismBaseEquiv B C φ hB hC hepi).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_epimorphismBaseEquiv B C φ hB hC hepi,
      continuous_epimorphismBaseEquiv_symm B C φ hB hC hepi⟩

/-- `epimorphismBaseEquiv` commutes with `inl`. -/
@[simp]
theorem epimorphismBaseEquiv_inl
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) (b : B) :
    epimorphismBaseEquiv B C φ hB hC hepi (inl A B C b) = inl A' B C b := by
  simp [epimorphismBaseEquiv, epimorphismBaseTo]

/-- `epimorphismBaseEquiv` commutes with `inr`. -/
@[simp]
theorem epimorphismBaseEquiv_inr
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) (c : C) :
    epimorphismBaseEquiv B C φ hB hC hepi (inr A B C c) = inr A' B C c := by
  simp [epimorphismBaseEquiv, epimorphismBaseTo]

/-- `(epimorphismBaseEquiv …).symm` commutes with `inl`. -/
@[simp]
theorem epimorphismBaseEquiv_symm_inl
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) (b : B) :
    (epimorphismBaseEquiv B C φ hB hC hepi).symm (inl A' B C b) = inl A B C b := by
  simp [epimorphismBaseEquiv, epimorphismBaseInv]

/-- `(epimorphismBaseEquiv …).symm` commutes with `inr`. -/
@[simp]
theorem epimorphismBaseEquiv_symm_inr
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) (c : C) :
    (epimorphismBaseEquiv B C φ hB hC hepi).symm (inr A' B C c) = inr A B C c := by
  simp [epimorphismBaseEquiv, epimorphismBaseInv]

/-- `epimorphismBaseEquiv` sends `b ⊗ₜ[A] c` to `b ⊗ₜ[A'] c`. -/
theorem epimorphismBaseEquiv_tmul
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) (b : B) (c : C) :
    epimorphismBaseEquiv B C φ hB hC hepi (toCompletion A B C (b ⊗ₜ[A] c)) =
      toCompletion A' B C (b ⊗ₜ[A'] c) := by
  simp

end EpimorphismBase

end CompletedTensor

namespace Pair.completedTensor

section EpimorphismBasePlus

variable {A : Type*} {A' : Type*} {B : Type v} {C : Type w}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra A' B] [Algebra A' C]
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing A'] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A' B)] [IsAdicHom (algebraMap A' C)]
  (φ : A →+* A')
  (hB : (algebraMap A' B).comp φ = algebraMap A B)
  (hC : (algebraMap A' C).comp φ = algebraMap A C)

/-- `epimorphismBaseEquiv` preserves membership in the completed tensor plus ring. -/
@[simp]
theorem epimorphismBaseEquiv_mem_plus_iff (PB : Pair B) (PC : Pair C)
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h)
    (x : CompletedTensor A B C) :
    CompletedTensor.epimorphismBaseEquiv B C φ hB hC hepi x ∈ (PB.completedTensor A' PC).plus ↔
      x ∈ (PB.completedTensor A PC).plus := by
  have _ := (PB.completedTensor A PC).isRingOfIntegralElements.isIntegrallyClosedIn
  have _ := (PB.completedTensor A' PC).isRingOfIntegralElements.isIntegrallyClosedIn
  constructor
  · intro hx
    have hle := PB.completedTensor_plus_le_comap (A := A') PC
      ((PB.completedTensor A PC).plus.toAddSubgroup.isClosed_of_isOpen
        (PB.completedTensor A PC).isRingOfIntegralElements.isOpen)
      (f := ((CompletedTensor.epimorphismBaseEquiv B C φ hB hC hepi).symm :
        CompletedTensor A' B C →+* CompletedTensor A B C))
      (CompletedTensor.continuous_epimorphismBaseEquiv_symm B C φ hB hC hepi)
      (fun b hb ↦ by simpa using PB.inl_mem_completedTensor_plus (A := A) PC hb)
      (fun c hc ↦ by simpa using PB.inr_mem_completedTensor_plus (A := A) PC hc)
      hx
    simpa using hle
  · intro hx
    exact PB.completedTensor_plus_le_comap (A := A) PC
      ((PB.completedTensor A' PC).plus.toAddSubgroup.isClosed_of_isOpen
        (PB.completedTensor A' PC).isRingOfIntegralElements.isOpen)
      (f := (CompletedTensor.epimorphismBaseEquiv B C φ hB hC hepi :
        CompletedTensor A B C →+* CompletedTensor A' B C))
      (CompletedTensor.continuous_epimorphismBaseEquiv B C φ hB hC hepi)
      (fun b hb ↦ by simpa using PB.inl_mem_completedTensor_plus (A := A') PC hb)
      (fun c hc ↦ by simpa using PB.inr_mem_completedTensor_plus (A := A') PC hc)
      hx

/-- `epimorphismBaseEquiv` carries `(PB.completedTensor A PC).plus` onto
`(PB.completedTensor A' PC).plus`. -/
theorem map_epimorphismBaseEquiv_plus (PB : Pair B) (PC : Pair C)
    (hepi : ∀ (g h : A' →+* CompletedTensor A B C), Continuous g → Continuous h →
      g.comp φ = h.comp φ → g = h) :
    (PB.completedTensor A PC).plus.map
        (CompletedTensor.epimorphismBaseEquiv B C φ hB hC hepi :
          CompletedTensor A B C →+* CompletedTensor A' B C) =
      (PB.completedTensor A' PC).plus := by
  ext y
  rw [Subring.mem_map_equiv]
  have h := (epimorphismBaseEquiv_mem_plus_iff φ hB hC PB PC hepi
    ((CompletedTensor.epimorphismBaseEquiv B C φ hB hC hepi).symm y)).symm
  simpa using h

end EpimorphismBasePlus

end Pair.completedTensor

end TauCeti.Huber

end
