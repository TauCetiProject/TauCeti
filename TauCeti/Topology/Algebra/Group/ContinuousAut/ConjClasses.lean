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
instance : MulAction (ContinuousAut G) (ConjClasses G) :=
  MulAction.compHom (ConjClasses G) (toMulAut : ContinuousAut G →* MulAut G)

/-- The action of a continuous automorphism on a conjugacy class is computed on a
representative. -/
@[simp]
theorem smul_conjClasses_mk (φ : ContinuousAut G) (x : G) :
    φ • ConjClasses.mk x = ConjClasses.mk (φ x) := by
  rw [MulAction.compHom_smul_def, mulAut_smul_conjClasses_mk]
  simp only [coe_toMulAut]

variable [SeparatelyContinuousMul G]

/-- Inner automorphisms fix every conjugacy class. -/
@[simp]
theorem conj_smul_conjClasses (g : G) (c : ConjClasses G) : conj g • c = c := by
  rw [MulAction.compHom_smul_def, toMulAut_conj, mulAut_conj_smul_conjClasses]

end ContinuousAut

variable [SeparatelyContinuousMul G]

namespace ContinuousOut

/-- The action of continuous automorphisms on conjugacy classes factors through
continuous outer automorphisms. -/
instance : MulAction (ContinuousOut G) (ConjClasses G) :=
  MulAction.compHom (ConjClasses G) <|
    QuotientGroup.lift (ContinuousAut.conj : G →* ContinuousAut G).range
      (MulAction.toPermHom (ContinuousAut G) (ConjClasses G)) (by
        rintro φ ⟨g, rfl⟩
        exact MonoidHom.mem_ker.mpr <| Equiv.ext fun c => by
          simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply,
            Equiv.Perm.one_apply] using ContinuousAut.conj_smul_conjClasses g c)

/-- The outer action is computed using any representative continuous automorphism. -/
theorem mk_smul_conjClasses (φ : ContinuousAut G) (c : ConjClasses G) :
    (mk φ) • c = φ • c := by
  rw [show mk φ = (φ : ContinuousOut G) from rfl]
  rw [MulAction.compHom_smul_def, QuotientGroup.lift_mk, Equiv.Perm.smul_def,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]

/-- On the class of an element, the outer action sends it to the class of its image. -/
theorem mk_smul_mk (φ : ContinuousAut G) (x : G) :
    (mk φ) • ConjClasses.mk x = ConjClasses.mk (φ x) := by
  rw [mk_smul_conjClasses, ContinuousAut.smul_conjClasses_mk]

end ContinuousOut

end TauCeti
