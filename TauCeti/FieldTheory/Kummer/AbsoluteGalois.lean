/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The Kummer pairing with the absolute Galois group

Over a field containing a primitive `n`-th root of unity, the action of the absolute Galois
group on an `n`-th root of a unit gives a character into the `n`-th roots of unity of the field.
Its kernel is the open stabilizer of the radical, so it descends to the topological
abelianization. The resulting pairing is multiplicative in the unit as well and is the
common construction behind the archimedean and nonarchimedean norm-residue symbols.
-/

public section

noncomputable section

namespace TauCeti

variable (K : Type*) [Field K] (n : ℕ) [NeZero n]

/-- An auxiliary choice of an `n`-th root of a unit. -/
private def radical (b : Kˣ) : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (b : K))
    (NeZero.pos n)).choose

private theorem radical_pow (b : Kˣ) :
    radical K n b ^ n = algebraMap K (AlgebraicClosure K) (b : K) :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (b : K))
    (NeZero.pos n)).choose_spec

variable [HasEnoughRootsOfUnity K n]

/-- Descent of roots of unity from the algebraic closure to the base field. -/
private def rootsEquiv : rootsOfUnity n K ≃* rootsOfUnity n (AlgebraicClosure K) :=
  rootsOfUnityEquivOfPrimitiveRoots (algebraMap K (AlgebraicClosure K)).injective (by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
    exact ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).2 hζ⟩)

/-- The radical character before descent through the topological abelianization. -/
private def radicalCharacter (b : Kˣ) : Gal(AlgebraicClosure K/K) →* rootsOfUnity n K :=
  (rootsEquiv K n).symm.toMonoidHom.comp
    { toFun σ := rootsOfUnity.mkOfPowEq (σ (radical K n b) / radical K n b) (by
        rw [div_pow, ← map_pow, radical_pow, AlgEquiv.commutes, div_self (by simp)])
      map_one' := by
        ext
        simp [ne_zero_of_pow_eq_algebraMap (radical_pow K n b)]
      map_mul' σ τ := by
        ext
        simp only [rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul]
        exact σ.mul_apply_div_self_of_pow_eq τ (radical_pow K n b) }

private theorem algebraMap_radicalCharacter (b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    algebraMap K (AlgebraicClosure K) ((radicalCharacter K n b σ : Kˣ) : K) = σ β / β := by
  rw [← σ.apply_div_self_eq_of_pow_eq ((radical_pow K n b).trans hβ.symm)]
  simp [radicalCharacter, rootsEquiv, rootsOfUnityEquivOfPrimitiveRoots_symm_apply]

/-- The radical character on the topological abelianization. -/
private def radicalCharacterAb (b : Kˣ) :
    TopologicalAbelianization Gal(AlgebraicClosure K/K) →* rootsOfUnity n K := by
  letI : TopologicalSpace (rootsOfUnity n K) := ⊥
  haveI : DiscreteTopology (rootsOfUnity n K) := ⟨rfl⟩
  refine (TopologicalAbelianization.lift ⟨radicalCharacter K n b, ?_⟩).toMonoidHom
  apply MonoidHom.continuous_of_isOpen_ker
  have hker : (radicalCharacter K n b).ker =
      MulAction.stabilizer Gal(AlgebraicClosure K/K) (radical K n b) := by
    ext σ
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, ← Units.val_inj,
      ← (algebraMap K (AlgebraicClosure K)).injective.eq_iff,
      algebraMap_radicalCharacter K n b σ (radical_pow K n b)]
    simp only [Subgroup.coe_one, Units.val_one, map_one, MulAction.mem_stabilizer_iff,
      div_eq_one_iff_eq (ne_zero_of_pow_eq_algebraMap (radical_pow K n b))]
    rfl
  rw [hker]
  exact stabilizer_isOpen_of_isIntegral (K := K) (radical K n b)

private theorem algebraMap_radicalCharacterAb (b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    algebraMap K (AlgebraicClosure K)
      ((radicalCharacterAb K n b (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) :
        Kˣ) : K) = σ β / β := by
  let : TopologicalSpace (rootsOfUnity n K) := ⊥
  have : DiscreteTopology (rootsOfUnity n K) := ⟨rfl⟩
  unfold radicalCharacterAb
  change algebraMap K (AlgebraicClosure K) ((TopologicalAbelianization.lift
    (A := rootsOfUnity n K) _ (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) : Kˣ) : K) =
    σ β / β
  rw [TopologicalAbelianization.lift_mk]
  exact algebraMap_radicalCharacter K n b σ hβ

/-- The Kummer pairing of units with the topological abelianization of the absolute Galois group.
Its value at `b` and the class of `σ` is the root of unity `σ β / β`, where `β ^ n = b`. -/
def abelianizedKummerPairing :
    Kˣ →* (TopologicalAbelianization Gal(AlgebraicClosure K/K) →* rootsOfUnity n K) where
  toFun := radicalCharacterAb K n
  map_one' := by
    apply MonoidHom.ext
    intro q
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective (α := Gal(AlgebraicClosure K/K)) q
    apply ((algebraMap K (AlgebraicClosure K)).injective.comp rootsOfUnity.coe_injective)
    change algebraMap K (AlgebraicClosure K) ((radicalCharacterAb K n 1 _ : Kˣ) : K) = _
    rw [algebraMap_radicalCharacterAb K n 1 σ (β := 1) (by simp)]
    simp
  map_mul' b c := by
    apply MonoidHom.ext
    intro q
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective (α := Gal(AlgebraicClosure K/K)) q
    apply ((algebraMap K (AlgebraicClosure K)).injective.comp rootsOfUnity.coe_injective)
    change algebraMap K (AlgebraicClosure K) ((radicalCharacterAb K n (b * c) _ : Kˣ) : K) =
      algebraMap K (AlgebraicClosure K)
        (((radicalCharacterAb K n b _ * radicalCharacterAb K n c _) : Kˣ) : K)
    simp only [Units.val_mul, map_mul]
    rw [algebraMap_radicalCharacterAb K n (b * c) σ (β := radical K n b * radical K n c) (by
          rw [mul_pow, radical_pow, radical_pow, Units.val_mul, map_mul]),
      algebraMap_radicalCharacterAb K n b σ (radical_pow K n b),
      algebraMap_radicalCharacterAb K n c σ (radical_pow K n c), map_mul, mul_div_mul_comm]

variable {K n}

/-- In the algebraic closure the pairing is `σ β / β` for any `n`-th root `β` of `b`. -/
theorem algebraMap_abelianizedKummerPairing (b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    algebraMap K (AlgebraicClosure K)
      ((abelianizedKummerPairing K n b (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) :
        Kˣ) : K) = σ β / β :=
  algebraMap_radicalCharacterAb K n b σ hβ

/-- A representative of the Galois class moves every radical by the value of the pairing. -/
theorem abelianizedKummerPairing_spec (b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    σ β = algebraMap K (AlgebraicClosure K)
      ((abelianizedKummerPairing K n b (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) :
        Kˣ) : K) *
        β := by
  rw [algebraMap_abelianizedKummerPairing b σ hβ,
    div_mul_cancel₀ _ (ne_zero_of_pow_eq_algebraMap hβ)]

end TauCeti
