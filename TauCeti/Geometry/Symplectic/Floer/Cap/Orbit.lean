/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.Cap.Action
public import TauCeti.Geometry.Symplectic.Floer.Cap.Smoothing
public import TauCeti.Topology.Homotopy.AddCircle

/-!
# Capped one-periodic orbits on a closed manifold

The generators of the capped Hamiltonian Floer complex of a closed manifold `M` are the
contractible one-periodic orbits `x` of a time-dependent vector field `X`, for instance the
Hamiltonian vector field `X_H`, each equipped with a cap class: a disc bounding `x`, up to gluing
spheres of zero area and zero first Chern number. This file assembles these generators from the
periodic solutions of `X` (`TauCeti.contractiblePeriodicSolutions`) and the cap classes of based
loops (`TauCeti.Floer.SphericalCapClass`), and equips them with the capped action, in the form
taken by the completed modules `TauCeti.NovikovModule` and the product of class-indexed counts of
`TauCeti.Geometry.Symplectic.Floer.Cap.Product`.

* **The loop of an orbit.** A contractible `1`-periodic solution `x` traces the loop
  `TauCeti.orbitLoop x : t ↦ x t`, `t ∈ [0, 1]`, based at `x 0`. It is null-homotopic
  relative to its base point (`TauCeti.orbitLoop_homotopic_refl`), so it has raw caps, and
  when `X` is `C^∞` it has a smooth based cap
  (`TauCeti.Floer.exists_isSmoothBasedCap_orbitLoop`): the orbit is `C^∞`
  (`TauCeti.contMDiff_of_contMDiff_of_forall_hasMFDerivAt_timeDependent`) and every raw cap of a
  loop with a smooth periodic extension has a smooth representative
  (`TauCeti.Floer.exists_isSmoothBasedCap_iff`).
* **Cap classes with the orientation of discs.** The raw caps of a loop are oriented from the loop
  to their centre, and the torsor `TauCeti.Floer.SphericalCapClass ω c γ` glues a class `B` at the
  centre with that orientation, which lowers the capped action by the area of `B`
  (`TauCeti.Floer.SphericalCapClass.action_vadd`). Capped Floer theory glues `B` to the disc
  oriented from its centre to the loop, which raises the action by the area of `B` and the grading
  by `2 c₁(B)`; this is the convention of the product of class-indexed counts, whose Floer Novikov
  ring is `TauCeti.Floer.NovikovRing`. The cap classes of the orbit `x` with this orientation are
  `TauCeti.Floer.OrbitCapClass ω c x`: the same classes, with `B +ᵥ q` the recapping `(-B) +ᵥ q`
  of `SphericalCapClass` (`TauCeti.Floer.OrbitCapClass.toSphericalCapClass_vadd`). They form a
  torsor under the spherical period group `Γ`.
* **Capped orbits and their action.** The capped orbits are
  `TauCeti.Floer.CappedOrbit ω c X = Σ x, OrbitCapClass ω c x`. For a closed `C¹` two-form `σ`
  whose integral over spheres is `ω` of their Hurewicz classes, and a Hamiltonian `Ham`, the
  capped action `TauCeti.Floer.CappedOrbit.action` is the capped action of the cap class
  (`TauCeti.Floer.SphericalCapClass.action`). On the cap class of a smooth based cap `u` it is the
  capped action `∫ D^* σ + ∫₀¹ Ham(t, x(t)) dt` of the disc `D` swept by `u` from its centre to `x`
  (`TauCeti.Floer.CappedOrbit.action_mk_homotopyClass`), and it obeys the recapping law
  `A(B +ᵥ q) = A(q) + ω(B)` (`TauCeti.Floer.CappedOrbit.action_vadd`). This is the equivariance
  `F ⟨x, B +ᵥ q⟩ = F ⟨x, q⟩ - (-area) B` of a potential for the periods `-area` under which the
  completed combinations of capped orbits, `NovikovModule R (CappedOrbit.action …)`, are a module
  over the Floer Novikov ring, free on any choice of reference caps when there are finitely many
  contractible orbits (`TauCeti.NovikovModule.basis`), as for a Hamiltonian whose contractible
  orbits are nondegenerate (`finite_contractiblePeriodicSolutions_hamiltonianVectorField` in the
  namespace `TauCeti.SmoothTwoForm.IsNondegenerate`).

## Main definitions

* `TauCeti.Floer.OrbitCapClass`: the cap classes of the orbit, with the orientation of discs.
* `TauCeti.Floer.CappedOrbit`: the capped contractible orbits.
* `TauCeti.Floer.CappedOrbit.action`: the capped action of a capped orbit.

## Main results

* `TauCeti.Floer.exists_isSmoothBasedCap_orbitLoop`: the loop of an orbit of a `C^∞` field has a
  smooth based cap.
* `TauCeti.Floer.CappedOrbit.action_vadd`: the recapping law of the capped action.
* `TauCeti.Floer.CappedOrbit.action_mk_homotopyClass`: the action of the class of a smooth cap is
  the capped action of its disc.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, Section 3 (the capped orbits generating the Floer
  complex over the Novikov ring).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 12.1 (Floer homology of a closed symplectic manifold).
-/

public section

noncomputable section

open Function Set AlgebraicTopology HomotopyGroup
-- `ω` names the area homomorphism here, so the `ContDiff` scope, whose notation includes `ω`, is
-- not opened, and smoothness `∞` is written out.
open scoped Manifold Topology Topology.Homotopy

namespace TauCeti.Floer

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {X : ℝ → (x : M) → TangentSpace I x}

/-! ### The loop of a contractible orbit -/

instance (x : contractiblePeriodicSolutions X 1) : Nonempty (RawCap (orbitLoop x)) :=
  RawCap.nonempty_iff.2 (orbitLoop_homotopic_refl x)

/-- **Orbits of a smooth field have smooth caps.** If the time-dependent field `X` is `C^∞`, the
loop of every contractible `1`-periodic solution has a smooth based cap. -/
theorem exists_isSmoothBasedCap_orbitLoop [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (x : contractiblePeriodicSolutions X 1) : ∃ u, IsSmoothBasedCap I (orbitLoop x) u :=
  exists_isSmoothBasedCap_iff.2 ⟨orbitLoop_homotopic_refl x, x.val,
    contMDiff_of_contMDiff_of_forall_hasMFDerivAt_timeDependent (n := ⊤) le_top hX
      (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset x.property)).1,
    periodic_of_mem_periodicSolutions (contractiblePeriodicSolutions_subset x.property),
        fun t ↦ by simp⟩

/-! ### Cap classes with the orientation of discs -/

variable (ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℝ)
  (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℤ)

/-- The **cap classes of a contractible orbit** `x`, with the orientation of discs: the cap
classes `TauCeti.Floer.SphericalCapClass ω c (orbitLoop x)`, on which a class `B` of the period
group acts by gluing it to the disc oriented from its centre to the orbit, the recapping `(-B) +ᵥ q`
of `SphericalCapClass` (`TauCeti.Floer.OrbitCapClass.toSphericalCapClass_vadd`). -/
def OrbitCapClass (x : contractiblePeriodicSolutions X 1) : Type :=
  SphericalCapClass ω c (orbitLoop x)

namespace OrbitCapClass

variable {ω c} {x : contractiblePeriodicSolutions X 1}

/-- The identification of the cap classes of an orbit with the cap classes of its loop. -/
def toSphericalCapClass : OrbitCapClass ω c x ≃ SphericalCapClass ω c (orbitLoop x) :=
  Equiv.refl _

instance : VSub (SphericalPeriodGroup ω c) (OrbitCapClass ω c x) :=
  ⟨fun q' q ↦ -(toSphericalCapClass q' -ᵥ toSphericalCapClass q)⟩

/-- Two orbit cap classes differ by minus the class by which the corresponding cap classes of the
loop differ. -/
theorem vsub_def (q' q : OrbitCapClass ω c x) :
    q' -ᵥ q = -(toSphericalCapClass q' -ᵥ toSphericalCapClass q) :=
  (rfl)

variable [PathConnectedSpace M]

instance : VAdd (SphericalPeriodGroup ω c) (OrbitCapClass ω c x) :=
  ⟨fun B q ↦ toSphericalCapClass.symm ((-B) +ᵥ toSphericalCapClass q)⟩

/-- **Recapping with the orientation of discs.** Gluing `B` to an orbit cap class is gluing `-B`
to the corresponding cap class of the loop. -/
@[simp]
theorem toSphericalCapClass_vadd (B : SphericalPeriodGroup ω c) (q : OrbitCapClass ω c x) :
    toSphericalCapClass (B +ᵥ q) = (-B) +ᵥ toSphericalCapClass q :=
  Equiv.apply_symm_apply _ _

instance : AddTorsor (SphericalPeriodGroup ω c) (OrbitCapClass ω c x) where
  vadd B q := B +ᵥ q
  zero_vadd q := toSphericalCapClass.injective (by simp)
  add_vadd B B' q := toSphericalCapClass.injective (by
    simp only [toSphericalCapClass_vadd, neg_add, add_vadd])
  vsub q' q := q' -ᵥ q
  vsub_vadd' q' q := toSphericalCapClass.injective (by simp [vsub_def])
  vadd_vsub' B q := by simp [vsub_def]
  nonempty := ⟨toSphericalCapClass.symm
    (Classical.arbitrary (SphericalCapClass ω c (orbitLoop x)))⟩

end OrbitCapClass

/-! ### Capped orbits and their action -/

/-- The **capped contractible `1`-periodic orbits** of `X`: pairs of a contractible orbit and a cap
class of it, with the orientation of discs. They are the generators of the capped Floer complex. -/
abbrev CappedOrbit (X : ℝ → (x : M) → TangentSpace I x) : Type :=
  Σ x : contractiblePeriodicSolutions X 1, OrbitCapClass ω c x

namespace CappedOrbit

variable {ω c} [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [CompactSpace M] [T2Space M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
  {σ : RoughForm I M ℝ 2} (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0)
  (hω : ∀ y a, ω (hurewiczIntHom M y 1 a) = sphereIntegralHom y hσ hdσ a) (Ham : ℝ → M → ℝ)

/-- The **capped action** of a capped orbit `⟨x, q⟩`, for a closed `C¹` two-form `σ` whose
integral over spheres is `ω` of their Hurewicz classes (`hω`) and a time-dependent Hamiltonian
`Ham`: the capped action `∫ D^* σ + ∫₀¹ Ham(t, x(t)) dt` of the discs `D` of the class `q`
(`TauCeti.Floer.SphericalCapClass.action`, characterized by
`TauCeti.Floer.CappedOrbit.action_mk_homotopyClass`). -/
def action (p : CappedOrbit ω c X) : ℝ :=
  SphericalCapClass.action hσ hdσ (hω (p.1.val 0)) Ham (exists_isSmoothBasedCap_orbitLoop hX p.1)
    (OrbitCapClass.toSphericalCapClass p.2)

/-- The action of a capped orbit is the action of its cap class
(`TauCeti.Floer.SphericalCapClass.action`). -/
theorem action_def (p : CappedOrbit ω c X) :
    action hX hσ hdσ hω Ham p = SphericalCapClass.action hσ hdσ (hω (p.1.val 0)) Ham
      (exists_isSmoothBasedCap_orbitLoop hX p.1) (OrbitCapClass.toSphericalCapClass p.2) :=
  (rfl)

/-- **The action of a smooth cap.** On the cap class of a smooth based cap `u` of the orbit `x`,
the action is the capped action of `x` with the disc swept by `u` from its centre to `x`. -/
theorem action_mk_homotopyClass {x : contractiblePeriodicSolutions X 1} {u : ℝ × ℝ → M}
    (hu : IsSmoothBasedCap I (orbitLoop x) u) :
    action hX hσ hdσ hω Ham
        ⟨x, OrbitCapClass.toSphericalCapClass.symm (SphericalCapClass.mk ω c hu.homotopyClass)⟩ =
      cappedLoopAction σ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) := by
  rw [action_def, Equiv.apply_symm_apply, SphericalCapClass.action_mk,
    ← RawCap.action_homotopyClass hσ hdσ Ham hu]

/-- **Two capped orbits of the same orbit differ by a class of the period group**, and their
actions by its area. -/
theorem action_sub_action (x : contractiblePeriodicSolutions X 1) (q' q : OrbitCapClass ω c x) :
    action hX hσ hdσ hω Ham ⟨x, q'⟩ - action hX hσ hdσ hω Ham ⟨x, q⟩ =
      PeriodGroup.area _ _ (q' -ᵥ q) := by
  rw [action_def, action_def, SphericalCapClass.action_sub_action, OrbitCapClass.vsub_def, map_neg]

variable [PathConnectedSpace M]

/-- **The recapping law.** Gluing a class `B` of the period group to the disc of a capped orbit
raises its action by the area of `B`. -/
@[simp]
theorem action_vadd (x : contractiblePeriodicSolutions X 1) (B : SphericalPeriodGroup ω c)
    (q : OrbitCapClass ω c x) :
    action hX hσ hdσ hω Ham ⟨x, B +ᵥ q⟩ =
      action hX hσ hdσ hω Ham ⟨x, q⟩ + PeriodGroup.area _ _ B := by
  rw [action_def, action_def, OrbitCapClass.toSphericalCapClass_vadd,
    SphericalCapClass.action_vadd, map_neg, neg_neg, add_comm]

/-- **The action is a potential for the Floer Novikov ring.** In the form taken by the completed
combinations `TauCeti.NovikovModule` over the Floer Novikov ring `TauCeti.Floer.NovikovRing`, whose
periods are minus the area, the recapping law reads `F ⟨x, B +ᵥ q⟩ = F ⟨x, q⟩ - (-area) B`. -/
theorem action_vadd_eq_sub (x : contractiblePeriodicSolutions X 1) (B : SphericalPeriodGroup ω c)
    (q : OrbitCapClass ω c x) :
    action hX hσ hdσ hω Ham ⟨x, B +ᵥ q⟩ =
      action hX hσ hdσ hω Ham ⟨x, q⟩ - (-PeriodGroup.area _ _) B := by
  rw [action_vadd, AddMonoidHom.neg_apply, sub_neg_eq_add]

end CappedOrbit

end TauCeti.Floer
