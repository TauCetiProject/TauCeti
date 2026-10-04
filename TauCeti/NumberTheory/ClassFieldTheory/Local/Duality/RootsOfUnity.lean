/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol

/-!
# The chosen-root comparison with Tate duality

A primitive `n`th root of unity in a field `F` identifies `μₙ` with its Tate dual
`Hom(μₙ, μₙ)`: the root with coordinate `c` acts by multiplication by `c`. This is an
isomorphism of Galois coefficient objects, and evaluation along it is precisely the named
Kummer coefficient pairing. Consequently the chosen-root local-symbol pairing is the degree
`(1, 1)` Tate-duality pairing under this coefficient isomorphism. For a local field with its
local invariant, this specializes to the Hilbert pairing.

This comparison relates the degree `(1, 1)` cyclic-coefficient case of local Tate duality
to nondegeneracy of the Hilbert pairing. The coefficient isomorphism itself is valid over any
field containing the chosen primitive root; it needs neither a local-field structure nor an
invariant map. The cohomological comparison holds for
every identification of `H²(F, μₙ)` with `ZMod n`.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.6).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory

universe u

variable {n : ℕ} [NeZero n] {F : Type u} [Field F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ n)

attribute [local instance] TopRep.distribMulAction

/-- The chosen-root map `μₙ → Hom(μₙ, μₙ)`: a root with coordinate `c` acts by scalar
multiplication by `c`. Its evaluation is the Kummer coefficient pairing. -/
def muNRepToTateDual : muNRep n F ⟶ tateDual (muNRep n F) :=
  ConcreteCategory.ofHom
    ⟨⟨((tateDualEquiv (muNRep n F)).symm.toAddMonoidHom.comp
        (LinearMap.toAddMonoidHom'.comp
          (kummerCupPairing ζ hζ).bil.toAddMonoidHom)).toZModLinearMap n,
      continuous_of_discreteTopology⟩,
      fun g => ContinuousLinearMap.ext fun x => by
        apply (tateDualEquiv (muNRep n F)).injective
        ext y
        simp only [ContinuousLinearMap.comp_apply,
          muNRep_ρ_apply_eq_self hζ, tateDualEquiv_ρ_apply]⟩

/-- Evaluation of the chosen-root dual map is the named Kummer coefficient pairing. -/
@[simp]
theorem tateDualEquiv_muNRepToTateDual_apply (x y : (muNRep n F).V) :
    tateDualEquiv (muNRep n F) ((muNRepToTateDual ζ hζ).hom x) y =
      (kummerCupPairing ζ hζ).bil x y := by
  have hmap : (muNRepToTateDual ζ hζ).hom x =
      (tateDualEquiv (muNRep n F)).symm
        ((kummerCupPairing ζ hζ).bil x).toAddMonoidHom :=
    -- The bundled continuous linear map was constructed from this additive homomorphism.
    (rfl)
  rw [hmap, AddEquiv.apply_symm_apply, LinearMap.toAddMonoidHom_coe]

/-- The chosen-root map identifies `μₙ` with its Tate dual. -/
theorem muNRepToTateDual_bijective : Function.Bijective (muNRepToTateDual ζ hζ).hom := by
  let e := (muNRepEquivTrivialFp n F hζ).trans (trivialFpEquiv n _).toAddEquiv
  have hpair (c : ZMod n) (y : (muNRep n F).V) :
      (kummerCupPairing ζ hζ).bil (e.symm c) y = c • y :=
    kummerCupPairing_bil_apply_zmod ζ hζ c y
  have hright (x : (muNRep n F).V) :
      (kummerCupPairing ζ hζ).bil x (e.symm 1) = x := by
    rw [kummerCupPairing_bil_comm, hpair, one_smul]
  constructor
  · intro x y h
    have := congrArg (fun φ => tateDualEquiv (muNRep n F) φ (e.symm 1)) h
    simpa only [tateDualEquiv_muNRepToTateDual_apply, hright] using this
  · intro φ
    refine ⟨tateDualEquiv (muNRep n F) φ (e.symm 1), ?_⟩
    apply (tateDualEquiv (muNRep n F)).injective
    ext y
    obtain ⟨c, rfl⟩ := e.symm.surjective y
    rw [tateDualEquiv_muNRepToTateDual_apply, kummerCupPairing_bil_comm, hpair,
      ← ZMod.map_smul (tateDualEquiv (muNRep n F) φ) c (e.symm 1),
      ← ZMod.map_smul e.symm c 1, smul_eq_mul, mul_one]

/-- The chosen-root identification with the Tate dual, as an isomorphism of coefficient objects. -/
def muNRepIsoTateDual : muNRep n F ≅ tateDual (muNRep n F) :=
  let e := LinearEquiv.ofBijective
    (muNRepToTateDual ζ hζ).hom.toContinuousLinearMap.toLinearMap
    (muNRepToTateDual_bijective ζ hζ)
  { hom := muNRepToTateDual ζ hζ
    inv := ConcreteCategory.ofHom
      ⟨⟨e.symm.toLinearMap, continuous_of_discreteTopology⟩,
        fun g => ContinuousLinearMap.ext fun φ => e.injective <| by
          -- The inverse intertwines because the forward coefficient map does.
          calc
            e (e.symm ((tateDual (muNRep n F)).ρ g φ)) =
                (tateDual (muNRep n F)).ρ g φ := e.apply_symm_apply _
            _ = (tateDual (muNRep n F)).ρ g (e (e.symm φ)) := by
              rw [e.apply_symm_apply]
            _ = e ((muNRep n F).ρ g (e.symm φ)) :=
              (TopRep.hom_comm_apply (muNRepToTateDual ζ hζ) g (e.symm φ)).symm⟩
    hom_inv_id := by ext x; exact e.symm_apply_apply x
    inv_hom_id := by ext φ; exact e.apply_symm_apply φ }

/-- The forward map of the chosen-root coefficient isomorphism is `muNRepToTateDual`. -/
@[simp]
theorem muNRepIsoTateDual_hom : (muNRepIsoTateDual ζ hζ).hom = muNRepToTateDual ζ hζ :=
  (rfl)

/-- The inverse chosen-root map evaluates a homomorphism at the chosen primitive root. -/
@[simp]
theorem muNRepIsoTateDual_inv_apply (φ : (tateDual (muNRep n F)).V) :
    (muNRepIsoTateDual ζ hζ).inv φ = tateDualEquiv (muNRep n F) φ
      ((muNRepEquivTrivialFp n F hζ).symm ((trivialFpEquiv n _).symm 1)) := by
  let E := muNRepIsoTateDual ζ hζ
  let a := (muNRepEquivTrivialFp n F hζ).symm ((trivialFpEquiv n _).symm 1)
  have hforward : (muNRepToTateDual ζ hζ).hom (E.inv φ) = φ := by
    simpa only [E, muNRepIsoTateDual_hom] using Iso.inv_hom_id_apply E φ
  have ha (x : (muNRep n F).V) : (kummerCupPairing ζ hζ).bil x a = x := by
    rw [kummerCupPairing_bil_comm, kummerCupPairing_bil_apply_zmod, one_smul]
  have h := congrArg (fun ψ => tateDualEquiv (muNRep n F) ψ a) hforward
  simpa only [tateDualEquiv_muNRepToTateDual_apply, ha] using h

/-- The degree `(1, 1)` Tate-duality pairing, read through the chosen-root coefficient
isomorphism, is the chosen-root local-symbol pairing for the identification `tr`.
For a local field with `tr` its local invariant, this is the cohomological Hilbert pairing. -/
theorem tateDualityPairing_muNRepToTateDual
    (tr : _root_.continuousCohomology.{0, u, u} 2 (muNRep n F) ≃+ ZMod n)
    (x y : _root_.continuousCohomology.{0, u, u} 1 (muNRep n F)) :
    tateDualityPairing (muNRep n F) tr 1 1 rfl
        ((ContinuousCohomology.coeffMap (muNRepToTateDual ζ hζ) 1).hom x) y =
      localSymbol (kummerCupPairing ζ hζ) tr x y := by
  have h := (kummerCupPairing ζ hζ).cup_coeffMap
    (tateEvaluationPairing (muNRep n F)) (muNRepToTateDual ζ hζ) (𝟙 _) (𝟙 _)
    (fun a b => by simp only [tateEvaluationPairing_bil,
      tateDualEquiv_muNRepToTateDual_apply, CategoryTheory.id_apply]) 1 1 x y
  simp only [ContinuousCohomology.coeffMap_id, CategoryTheory.id_apply] at h
  simpa only [tateDualityPairing_def, localSymbol_apply] using congrArg tr h.symm

end TauCeti.ClassFieldTheory
