/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Rotation
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.TorusClass
public import TauCeti.Data.ZMod.IntUnitsPower

/-!
# The torus sign local system on the free loop space

Let `Q` be a space and `c : H₂(Q; ℤ) → ℤ/2` an additive map, for instance the pairing with a mod-2
cohomology class such as the second Stiefel–Whitney class `w₂` of a manifold. A loop `Λ` of free
loops of `Q` sweeps out a torus `(s, t) ↦ Λ t s` in `Q`, whose class in `H₂(Q; ℤ)` is the torus
class of `Λ` (`TauCeti.MooreFreeLoopSpace.torusClassHom`). The **torus sign** of `c` at a free
Moore loop `γ` is the rank-one local system on `(𝓛Q, γ)` along which a loop `Λ` of free loops acts
by the sign

`(-1) ^ c(torus class of Λ)`

(`TauCeti.RankOneLocalSystem.torusSign`, `TauCeti.RankOneLocalSystem.torusSign_ρ_apply`), with
coefficients in any commutative ring `R`. For `c = ⟨w₂(TQ), -⟩` this is the sign system `σ` of the
degree-zero twist `η₀ = σ ⊗ ev₀^*(o_Q^{-1}) ⊗ ev₀^*(o_Q^{-w})` of Barraud–Damian–Humilière–Oancea
(§§1.5 and 4.1), which enters their Viterbo isomorphism with DG coefficients for `T^*Q`; the
other two factors are `TauCeti.RankOneLocalSystem.viterboOrientationTwist`. The sign only depends
on `c` through its values on torus classes.

The torus sign is additive in `c`: `σ_{c + c'} = σ_c ⊗ σ_{c'}` and `σ_0 = 1`
(`TauCeti.RankOneLocalSystem.torusSign_add`, `TauCeti.RankOneLocalSystem.torusSign_zero`), and it is
its own inverse. It is trivial exactly when `c` vanishes on the torus classes at `γ` or `2 = 0`
in `R` (`TauCeti.RankOneLocalSystem.torusSign_eq_one_iff`). At a constant loop the torus classes are
the Hurewicz classes of `π₂(Q, x)`, so there the torus sign is trivial exactly when `c` vanishes on
spherical classes or `2 = 0` (`TauCeti.RankOneLocalSystem.torusSign_const_eq_one_iff`).

Rotating a free loop once around itself sweeps out a torus that factors through the circle, so its
class vanishes and the torus sign acts trivially along the rotation of every loop
(`TauCeti.RankOneLocalSystem.torusSign_ρ_rotationLoop`).

A loop of constant loops sweeps out a degenerate torus, so the torus sign is trivial along the
constant loops: its pullback along the inclusion `Q → 𝓛Q` of the constant loops is trivial
(`TauCeti.RankOneLocalSystem.pullback_constMap_torusSign`). For `c = ⟨w₂(TQ), -⟩`, together with
`TauCeti.RankOneLocalSystem.pullback_constMap_viterboOrientationTwist`, this identifies the
pullback `i_Q^* η₀` of the Viterbo twist along the constant loops with `o_Q`.

The torus class, and so the torus sign, is defined for spaces `Q` in the lowest universe, as the
singular torus class `TauCeti.freeLoopTorusClassHom` is.

## Main definitions

* `TauCeti.MooreFreeLoopSpace.torusSignCharacter c γ`: the character `π₁(𝓛Q, γ) →* ℤˣ` sending a
  loop of free loops to `(-1) ^ c(torus class)`.
* `TauCeti.RankOneLocalSystem.torusSign R c γ`: the rank-one local system on `(𝓛Q, γ)` with this
  monodromy, read in `Rˣ`.

## Main results

* `TauCeti.RankOneLocalSystem.torusSign_ρ_apply`, `TauCeti.RankOneLocalSystem.monodromy_torusSign`:
  its action and its monodromy.
* `TauCeti.RankOneLocalSystem.torusSign_zero`, `TauCeti.RankOneLocalSystem.torusSign_add`,
  `TauCeti.RankOneLocalSystem.inv_torusSign`: it is additive in `c` and its own inverse.
* `TauCeti.RankOneLocalSystem.torusSign_eq_one_iff`,
  `TauCeti.RankOneLocalSystem.torusSign_const_eq_one_iff`: when it is trivial, and at a constant
  loop in terms of the Hurewicz classes of `π₂`.
* `TauCeti.RankOneLocalSystem.torusSign_ρ_rotationLoop`: it is trivial along the rotation of every
  loop.
* `TauCeti.RankOneLocalSystem.pullback_constMap_torusSign`: it is trivial along the constant
  loops.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, EMS (2015), §§5–6 (the local system on the free
  loop space in the Viterbo isomorphism).
-/

public section

noncomputable section

namespace TauCeti

open AlgebraicTopology MooreFreeLoopSpace

variable {Q : Type} [TopologicalSpace Q] (R : Type*) [CommRing R]
  (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of Q) →+
    ZMod 2)

namespace MooreFreeLoopSpace

/-- **The torus sign character** of an additive map `c : H₂(Q; ℤ) → ℤ/2` at a free Moore loop `γ`:
the character of `π₁(𝓛Q, γ)` sending a loop of free loops to `(-1) ^ c(a)`, where `a` is the class
of the torus it sweeps out. -/
def torusSignCharacter (γ : MooreFreeLoopSpace Q) :
    FundamentalGroup (MooreFreeLoopSpace Q) γ →* ℤˣ where
  toFun g := hilbertSign (c (γ.torusClassHom (Additive.ofMul g)))
  map_one' := by rw [ofMul_one, map_zero, map_zero, hilbertSign_zero]
  map_mul' g h := by rw [ofMul_mul, map_add, map_add, hilbertSign_add]

@[simp]
theorem torusSignCharacter_apply (γ : MooreFreeLoopSpace Q)
    (g : FundamentalGroup (MooreFreeLoopSpace Q) γ) :
    torusSignCharacter c γ g = hilbertSign (c (γ.torusClassHom (Additive.ofMul g))) :=
  (rfl)

/-- The torus sign character is trivial exactly when `c` vanishes on the torus classes of all
loops of free loops at `γ`. -/
theorem torusSignCharacter_eq_one_iff (γ : MooreFreeLoopSpace Q) :
    torusSignCharacter c γ = 1 ↔ ∀ g, c (γ.torusClassHom (Additive.ofMul g)) = 0 := by
  simp only [MonoidHom.ext_iff, torusSignCharacter_apply, MonoidHom.one_apply,
    hilbertSign_eq_one_iff]

end MooreFreeLoopSpace

namespace RankOneLocalSystem

/-- **The torus sign local system** of an additive map `c : H₂(Q; ℤ) → ℤ/2` at a free Moore loop
`γ`: the rank-one local system on `(𝓛Q, γ)`, with coefficients in `R`, along which a loop of free
loops acts by `(-1) ^ c(a)`, where `a` is the class of the torus it sweeps out. For `c` the pairing
with the second Stiefel–Whitney class of a manifold `Q`, this is the sign factor `σ` of the
degree-zero Viterbo twist on the free loop space of `Q`. -/
def torusSign (γ : MooreFreeLoopSpace Q) : RankOneLocalSystem (MooreFreeLoopSpace Q) γ R :=
  ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (torusSignCharacter c γ))

variable {R}

theorem torusSign_def (γ : MooreFreeLoopSpace Q) :
    torusSign R c γ =
      ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (torusSignCharacter c γ)) :=
  (rfl)

/-- **The action on the torus sign**: a Moore loop `Λ` of free loops acts by `(-1) ^ c(a)`, read in
`Rˣ`, where `a` is the torus class of `Λ`. -/
theorem torusSign_ρ_apply (γ : MooreFreeLoopSpace Q)
    (Λ : MooreLoopSpace (MooreFreeLoopSpace Q) γ) :
    (torusSign R c γ).ρ Λ = Units.map (Int.castRingHom R).toMonoidHom
      (hilbertSign (c (γ.torusClassHom
        (Additive.ofMul (MooreLoopSpace.fundamentalGroupHom γ Λ))))) := by
  rw [torusSign_def, ofMonodromy_unitsMap_comp_ρ_apply, torusSignCharacter_apply]

/-- The monodromy of the torus sign is the torus sign character, read in `Rˣ`. -/
@[simp]
theorem monodromy_torusSign (γ : MooreFreeLoopSpace Q) :
    (torusSign R c γ).monodromy =
      (Units.map (Int.castRingHom R).toMonoidHom).comp (torusSignCharacter c γ) :=
  monodromy_ofMonodromy _

/-- The torus sign of the zero map is trivial. -/
@[simp]
theorem torusSign_zero (γ : MooreFreeLoopSpace Q) : torusSign R 0 γ = 1 :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun Λ ↦ by simp [torusSign_ρ_apply]

/-- **The torus sign is additive in the class**: `σ_{c + c'} = σ_c ⊗ σ_{c'}`. -/
theorem torusSign_add
    (c' : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of Q) →+ ZMod 2) (γ : MooreFreeLoopSpace Q) :
    torusSign R (c + c') γ = torusSign R c γ * torusSign R c' γ :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun Λ ↦ by
    simp [torusSign_ρ_apply, hilbertSign_add]

/-- **The torus sign is its own inverse.** -/
@[simp]
theorem inv_torusSign (γ : MooreFreeLoopSpace Q) : (torusSign R c γ)⁻¹ = torusSign R c γ :=
  inv_ofMonodromy_unitsMap_comp _

/-- **The torus sign is trivial exactly when `c` vanishes on the torus classes at `γ`, or `2 = 0`
in `R`.** -/
theorem torusSign_eq_one_iff (γ : MooreFreeLoopSpace Q) :
    torusSign R c γ = 1 ↔
      (∀ g, c (γ.torusClassHom (Additive.ofMul g)) = 0) ∨ (2 : R) = 0 := by
  rw [torusSign_def, ofMonodromy_unitsMap_comp_eq_one_iff, torusSignCharacter_eq_one_iff]

/-- **Over a ring of characteristic two the torus sign is trivial.** -/
theorem torusSign_eq_one_of_two_eq_zero (h2 : (2 : R) = 0) (γ : MooreFreeLoopSpace Q) :
    torusSign R c γ = 1 :=
  (torusSign_eq_one_iff c γ).2 (.inr h2)

/-- **At a constant loop the torus sign sees exactly the spherical classes**: the torus sign at the
constant loop at `x` is trivial exactly when `c` vanishes on the Hurewicz classes of `π₂(Q, x)`, or
`2 = 0` in `R`. The torus classes of loops of free loops at a constant loop are the Hurewicz
classes of `π₂(Q, x)` (`TauCeti.MooreFreeLoopSpace.range_torusClassHom_const`). -/
theorem torusSign_const_eq_one_iff (x : Q) :
    torusSign R c (const x) = 1 ↔
      (∀ a : HomotopyGroup (Fin 2) Q x,
        c (HomotopyGroup.hurewiczIntHom Q x 1 (Additive.ofMul a)) = 0) ∨ (2 : R) = 0 := by
  have h := congrArg (fun S ↦ ∀ y ∈ S, c y = 0) (range_torusClassHom_const x)
  simp only [AddMonoidHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at h
  rw [← Additive.ofMul.forall_congr_right, ← Additive.ofMul.forall_congr_right] at h
  exact (torusSign_eq_one_iff c _).trans (or_congr_left h.to_iff)

/-- **The torus sign is trivial along the rotation of every loop**: the rotation loop of `γ` sweeps
out a torus whose class vanishes
(`TauCeti.MooreFreeLoopSpace.torusClassHom_fundamentalGroupHom_rotationLoop`). -/
@[simp]
theorem torusSign_ρ_rotationLoop (γ : MooreFreeLoopSpace Q) :
    (torusSign R c γ).ρ γ.rotationLoop = 1 := by
  rw [torusSign_ρ_apply, torusClassHom_fundamentalGroupHom_rotationLoop, map_zero,
    hilbertSign_zero, map_one]

/-- **Along the constant loops the torus sign is trivial**: its pullback along the inclusion
`Q → 𝓛Q` of the constant loops is the trivial local system, since a loop of constant loops sweeps
out a degenerate torus. -/
@[simp]
theorem pullback_constMap_torusSign (x : Q) :
    pullback (constMap Q) (constMap_apply x) (torusSign R c (const x)) = 1 :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun δ ↦ by
    simp [torusSign_ρ_apply, MooreLoopSpace.fundamentalGroupHom_map]

end RankOneLocalSystem

end TauCeti
