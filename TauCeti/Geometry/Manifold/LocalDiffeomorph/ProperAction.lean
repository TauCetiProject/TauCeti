/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Algebra.ProperAction.Basic
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Topology.Algebra.ProperAction.Injectivity

/-!
# Equivariant local diffeomorphisms into proper actions

`IsLocalDiffeomorphAt.exists_diffeomorph_smul_of_le_stabilizer` promotes an equivariant local
diffeomorphism to a diffeomorphism of invariant open neighbourhoods using
`ProperSMul.exists_isOpen_injOn_smul_of_le_stabilizer` and
`IsLocalDiffeomorph.diffeomorphOfInjective`.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, 2003, proof of Theorem 1.25.
-/

public section

open Filter Function Set TopologicalSpace
open scoped ContDiff Manifold Pointwise Topology

namespace IsLocalDiffeomorphAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {G : Type*} [Group G] [TopologicalSpace G]
  {EY HY Y : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
  {IY : ModelWithCorners 𝕜 EY HY} [TopologicalSpace Y] [ChartedSpace HY Y] [MulAction G Y]
  {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X] [MulAction G X]
  {n : ℕ∞ω} [ContinuousSMul G Y] [ContMDiffConstSMul IY n G Y]
  [ContMDiffConstSMul IX n G X] [ProperSMul G X]

/-- An equivariant `C^n` local diffeomorphism into a proper action that preserves the stabilizer
at `y` restricts to a diffeomorphism between invariant open neighbourhoods of the two orbits. -/
theorem exists_diffeomorph_smul_of_le_stabilizer {f : Y → X} {y : Y}
    (hf : IsLocalDiffeomorphAt IY IX n f y) (hequiv : ∀ (g : G) z, f (g • z) = g • f z)
    (hstab : MulAction.stabilizer G (f y) ≤ MulAction.stabilizer G y) :
    ∃ (U : Opens Y) (V : Opens X) (e : U ≃ₘ^n⟮IY, IX⟯ V),
      y ∈ U ∧ (∀ (g : G), MapsTo (g • ·) (U : Set Y) U) ∧ ∀ u : U, (e u : X) = f u := by
  obtain ⟨N, hN, hinj⟩ := hf.exists_mem_nhds_injOn
  obtain ⟨W, hW, hyW, hWN, hinjW⟩ := ProperSMul.exists_isOpen_injOn_smul_of_le_stabilizer
    hf.contMDiffAt.continuousAt hequiv hstab (inter_mem hN hf.eventually)
    (hinj.mono inter_subset_left)
  let U : Opens Y := ⟨(univ : Set G) • W, hW.smul_left⟩
  have hlocU : IsLocalDiffeomorph IY IX n (fun u : U ↦ f u) := by
    intro u
    obtain ⟨g, -, z, hz, hgz⟩ := mem_smul.mp u.property
    have hzloc : IsLocalDiffeomorphAt IY IX n f z := (hWN hz).2
    let A : Y ≃ₘ^n⟮IY, IY⟯ Y := Diffeomorph.constSmul IY n g
    let B : X ≃ₘ^n⟮IX, IX⟯ X := Diffeomorph.constSmul IX n g
    have hcomp : f ∘ A = B ∘ f := funext fun v ↦ by
      have hA : A v = g • v := Diffeomorph.constSmul_apply g v
      have hB : B (f v) = g • f v := Diffeomorph.constSmul_apply g (f v)
      exact (congrArg f hA).trans ((hequiv g v).trans hB.symm)
    have hgzloc : IsLocalDiffeomorphAt IY IX n f (A z) :=
      (hcomp.symm ▸ hzloc.comp (hg := B.isLocalDiffeomorph (f z))).of_comp_right
        (A.isLocalDiffeomorph z)
    have hAz : A z = (u : Y) := (Diffeomorph.constSmul_apply g z).trans hgz
    exact (TauCeti.isLocalDiffeomorph_subtype_val u).comp (hg := hAz ▸ hgzloc)
  have hinjU : Injective (fun u : U ↦ f u) := fun u v huv ↦
    Subtype.ext (hinjW u.property v.property huv)
  refine ⟨U, hlocU.image, hlocU.diffeomorphOfInjective hinjU, ?_, ?_,
    hlocU.coe_diffeomorphOfInjective_apply hinjU⟩
  · exact mem_smul.mpr ⟨1, mem_univ _, y, hyW, one_smul _ _⟩
  · intro g u hu
    obtain ⟨a, -, z, hz, rfl⟩ := mem_smul.mp hu
    exact mem_smul.mpr ⟨g * a, mem_univ _, z, hz, mul_smul _ _ _⟩

end IsLocalDiffeomorphAt
