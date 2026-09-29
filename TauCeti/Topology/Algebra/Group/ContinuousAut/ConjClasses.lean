/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic
public import TauCeti.Algebra.Group.Conj

/-!
# Continuous outer automorphisms acting on conjugacy classes

A continuous automorphism sends a conjugacy class to the class of its image. Inner
automorphisms fix every conjugacy class, so this action factors through the continuous
outer automorphism group. These actions are the basic interface for transporting
conjugacy-invariant data along outer actions of extensions.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace ContinuousAut

/-- A continuous automorphism acts on conjugacy classes by its underlying group
automorphism. -/
instance : MulAction (ContinuousAut G) (ConjClasses G) where
  smul φ c := ConjClasses.map φ.toMulEquiv.toMonoidHom c
  one_smul c := by
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    rfl
  mul_smul φ ψ c := by
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    rfl

/-- The action of a continuous automorphism on a conjugacy class is computed on a
representative. -/
@[simp]
theorem smul_conjClasses_mk (φ : ContinuousAut G) (x : G) :
    φ • ConjClasses.mk x = ConjClasses.mk (φ x) := by
  exact ConjClasses.map_mk _ x

variable [SeparatelyContinuousMul G]

/-- Inner automorphisms fix every conjugacy class. -/
@[simp]
theorem conj_smul_conjClasses (g : G) (c : ConjClasses G) : conj g • c = c := by
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
  rw [smul_conjClasses_mk]
  exact (ConjClasses.mk_eq_mk_iff_isConj.mpr
    (isConj_iff.mpr ⟨g, (conj_apply g x).symm⟩)).symm

end ContinuousAut

variable [SeparatelyContinuousMul G]

namespace ContinuousOut

/-- The action of continuous automorphisms on conjugacy classes factors through
continuous outer automorphisms. -/
instance : MulAction (ContinuousOut G) (ConjClasses G) where
  smul c x := Quotient.liftOn' c (fun φ : ContinuousAut G => φ • x) (by
    intro φ ψ h
    obtain ⟨g, hg⟩ := QuotientGroup.leftRel_apply.mp h
    have hinner : φ⁻¹ * ψ = ContinuousAut.conj g := hg.symm
    have hψ : ψ = φ * ContinuousAut.conj g := by
      calc
        ψ = φ * (φ⁻¹ * ψ) := by simp
        _ = φ * ContinuousAut.conj g := by rw [hinner]
    rw [hψ, mul_smul, ContinuousAut.conj_smul_conjClasses])
  one_smul x := by
    -- The quotient's identity is represented by the identity automorphism.
    change (1 : ContinuousAut G) • x = x
    exact one_smul _ x
  mul_smul c d x := by
    induction c using Quotient.inductionOn' with
    | h φ =>
      induction d using Quotient.inductionOn' with
      | h ψ =>
        -- Multiplication of quotient classes is represented by multiplication upstairs.
        change (φ * ψ) • x = φ • ψ • x
        exact mul_smul φ ψ x

/-- The outer action is computed using any representative continuous automorphism. -/
@[simp]
theorem mk_smul_conjClasses (φ : ContinuousAut G) (c : ConjClasses G) :
    (mk φ) • c = φ • c :=
  rfl

/-- On the class of an element, the outer action sends it to the class of its image. -/
@[simp]
theorem mk_smul_mk (φ : ContinuousAut G) (x : G) :
    (mk φ) • ConjClasses.mk x = ConjClasses.mk (φ x) := by
  rw [mk_smul_conjClasses, ContinuousAut.smul_conjClasses_mk]

end ContinuousOut

end TauCeti
