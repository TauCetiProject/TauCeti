/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.HilbertPairing
public import TauCeti.NumberTheory.LocalField.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.TrivialAction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Cup
import TauCeti.Algebra.Module.ZMod.Dual

/-!
# Local Tate duality for modules with trivial action

Let `K` be a nonarchimedean local field containing a primitive `n`th root of unity `ζ`. This file
proves Tate's local duality with values in `ℤ/n` for every finite module killed by `n` on which
`G_K` acts trivially. It first treats the trivial module `ℤ/n` itself, proving that
the duality maps `αᵢ : Hⁱ(G_K, ℤ/n) → Hom(H²⁻ⁱ(G_K, Hom(ℤ/n, ℤ/n)), H²(G_K, ℤ/n))` in degrees `0`
and `1` (`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`) are bijective, `α₂`
(`TauCeti.ContCohomology.dualityMap2`) being bijective for every group acting trivially. The root
`ζ` identifies the trivial coefficients `ℤ/n` with `μₙ`, so this is the duality of `μₙ` with itself,
and it is the base case from which local duality for a general finite module is reached by
Shapiro's lemma and the four lemma.

From `ℤ/n` the duality passes to every finite module `A` killed by `n` with trivial action
(`TauCeti.ClassFieldTheory.dualityMap0_bijective_of_isPrimitiveRoot` and its companions in degrees
`1` and `2`), by the dévissage of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Duality/TrivialAction.lean`: `A`
embeds into a free `ℤ/n`-module, along which the four lemma gives injectivity, and the injections
are bijections by counting, `H¹(G_K, ℤ/n)` being finite.

The arithmetic input is in degree `(1, 1)`: **the cup square on `H¹(G_K, ℤ/n)` is a perfect
pairing** (`TauCeti.ClassFieldTheory.cupFp_bijective_of_isPrimitiveRoot`). Through `ζ` it is the
cohomological Hilbert pairing along `kummerCupPairing ζ hζ`
(`TauCeti.ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup`), which separates
the points of its second variable (`TauCeti.ClassFieldTheory.separatingRight_localSymbol`). By
graded commutativity (`TauCeti.cupFp_eq_zero_comm`) it separates those of its first variable too,
and `H¹(G_K, ℤ/n)` and its `ℤ/n`-linear maps to `H²(G_K, ℤ/n) ≃ ℤ/n` (`h2FpEquivZMod`) are finite
of the same order, so the injection `a ↦ (a ⌣ -)` is a bijection. In degrees `(0, 2)` and `(2, 0)`
the duality maps are scalar multiplication on `H²(G_K, ℤ/n) ≃ ℤ/n`; `α₂` is bijective for every
group acting trivially (`TauCeti.ContCohomology.dualityMap2_zmod_bijective`), and `α₀` because
`H²(G_K, ℤ/n)` is `ℤ/n` (`TauCeti.ContCohomology.dualityMap0_zmod_bijective_of_addEquiv`).

The duality maps are stated for any topological group `H` isomorphic to `G_K`, the form in which an
open subgroup of the absolute Galois group of a smaller field, fixing a finite extension `K`,
appears in Shapiro's lemma.

## Main results

* `TauCeti.ClassFieldTheory.cupFp_bijective_of_isPrimitiveRoot`: the cup square on
  `H¹(G_K, ℤ/n)` is a perfect pairing when `K` contains a primitive `n`th root of unity.
* `TauCeti.ClassFieldTheory.dualityMap0_zmod_bijective_of_isPrimitiveRoot`,
  `TauCeti.ClassFieldTheory.dualityMap1_zmod_bijective_of_isPrimitiveRoot`: Tate's duality maps
  `α₀` and `α₁` at the trivial module `ℤ/n` are bijective, for any topological group isomorphic to
  `G_K`.
* `TauCeti.ClassFieldTheory.dualityMap0_bijective_of_isPrimitiveRoot`,
  `TauCeti.ClassFieldTheory.dualityMap1_bijective_of_isPrimitiveRoot`,
  `TauCeti.ClassFieldTheory.dualityMap2_bijective_of_isPrimitiveRoot`: Tate's duality maps with
  values in `ℤ/n` are bijective on every finite module killed by `n` with trivial action, for any
  topological group isomorphic to `G_K`.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.2, Theorem 2 and its proof.
* J.-P. Serre, *Local Fields*, GTM 67, Chapter XIV, §2.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)

include hζ

/-- **The cup square on `H¹(G_K, ℤ/n)` is a perfect pairing** when the nonarchimedean local field
`K` contains a primitive `n`th root of unity: `a ↦ (b ↦ a ⌣ b)` is a bijection from `H¹(G_K, ℤ/n)`
onto the `ℤ/n`-linear maps `H¹(G_K, ℤ/n) → H²(G_K, ℤ/n)`. Through the chosen-root identification
of `ℤ/n` with `μₙ` this is the perfectness of the Hilbert pairing. -/
theorem cupFp_bijective_of_isPrimitiveRoot :
    Function.Bijective (cupFp n (Field.absoluteGaloisGroup K)) := by
  have hn : IsUnit (n : K) := hζ.neZero'.out.isUnit
  have : NeZero (n : K) := ⟨hn.ne_zero⟩
  have hcard := (h2FpEquivZMod hζ).natCard_linearMap_zmod
    (M := cohomFp n (Field.absoluteGaloisGroup K) 1)
  have : Finite (cohomFp n (Field.absoluteGaloisGroup K) 1 →ₗ[ZMod n]
      cohomFp n (Field.absoluteGaloisGroup K) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  -- a class pairing to zero with every class on its left is zero, by the Hilbert pairing
  have hsep (b : cohomFp n (Field.absoluteGaloisGroup K) 1)
      (hb : ∀ a, cupFp n (Field.absoluteGaloisGroup K) a b = 0) : b = 0 := by
    obtain ⟨y, rfl⟩ := (muNRepCohomologyEquivTrivialFp n K hζ 1).surjective b
    rw [separatingRight_localSymbol hζ (h2MuEquivZMod K hn) y fun x => ?_, map_zero]
    rw [localSymbol_apply, ← (h2MuEquivZMod K hn).map_zero]
    refine congrArg _ ((muNRepCohomologyEquivTrivialFp n K hζ 2).injective ?_)
    rw [muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup, hb, map_zero]
  refine Function.Injective.bijective_of_nat_card_le
    ((injective_iff_map_eq_zero _).2 fun a ha => hsep a fun b => ?_) hcard.le
  -- `a ⌣ b` vanishes for every `b`, so `b ⌣ a` does too, by graded commutativity
  rw [cupFp_eq_zero_comm, ha, LinearMap.zero_apply]

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (φ : AbsoluteGaloisGroup K ≃ₜ* H) [DistribMulAction H (ZMod n)] [ContinuousSMul H (ZMod n)]
  (htriv : ∀ (h : H) (m : ZMod n), h • m = m)

include φ htriv

/-- `H²(H, ℤ/n) ≃+ ZMod n` for a topological group `H` isomorphic to `G_K`, through the local
invariant `h2FpEquivZMod`. -/
private noncomputable def h2ZModEquiv : H2 H (ZMod n) ≃+ ZMod n :=
  let ψ := (absoluteGaloisGroupRestrictEquiv K).trans φ
  have : LocallyCompactSpace H := ψ.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  (cohomFpAddEquivH2 n H htriv).symm.trans
    ((cohomFpLinearEquiv n ψ 2).symm.toAddEquiv.trans (h2FpEquivZMod hζ))

/-- **Tate's duality map `α₁` at the trivial module `ℤ/n` is bijective** for a topological group
`H` isomorphic to `G_K`, when the local field `K` contains a primitive `n`th root of unity:
`H¹(H, ℤ/n) → Hom(H¹(H, Hom(ℤ/n, ℤ/n)), H²(H, ℤ/n))` is a bijection. Under evaluation at `1` it is
the cup square, a perfect pairing by `cupFp_bijective_of_isPrimitiveRoot`. -/
theorem dualityMap1_zmod_bijective_of_isPrimitiveRoot :
    Function.Bijective (dualityMap1 H (ZMod n) (ZMod n)) := by
  let ψ := (absoluteGaloisGroupRestrictEquiv K).trans φ
  have : LocallyCompactSpace H := ψ.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  exact (dualityMap1_zmod_bijective_iff htriv).2 ((explicitCup11_mul_bijective_iff n H htriv).2
    ((cupFp_bijective_congr n _ ψ).1 (cupFp_bijective_of_isPrimitiveRoot hζ)))

/-- **Tate's duality map `α₀` at the trivial module `ℤ/n` is bijective** for a topological group
`H` isomorphic to `G_K`, when the local field `K` contains a primitive `n`th root of unity:
`H⁰(H, ℤ/n) → Hom(H²(H, Hom(ℤ/n, ℤ/n)), H²(H, ℤ/n))` is a bijection, since it is scalar
multiplication on `H²(H, ℤ/n)`, which is `ℤ/n` by the local invariant (`h2FpEquivZMod`). -/
theorem dualityMap0_zmod_bijective_of_isPrimitiveRoot :
    Function.Bijective (dualityMap0 H (ZMod n) (ZMod n)) :=
  dualityMap0_zmod_bijective_of_addEquiv htriv (h2ZModEquiv hζ φ htriv)

/-- `H¹(H, ℤ/n)` is finite for a topological group `H` isomorphic to `G_K`, when the local field
`K` contains a primitive `n`th root of unity. -/
private theorem finite_H1_zmod : Finite (H1 H (ZMod n)) := by
  have : NeZero (n : K) := ⟨hζ.neZero'.out⟩
  exact Finite.of_equiv _ ((cohomFpLinearEquiv n ((absoluteGaloisGroupRestrictEquiv K).trans φ)
    1).toAddEquiv.trans (cohomFpAddEquivH1 n H htriv)).toEquiv

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction H A] [ContinuousSMul H A] [Finite A] (hA : ∀ a : A, n • a = 0)
  (hAtriv : ∀ (h : H) (a : A), h • a = a)

include hA hAtriv

/-- **Tate's duality map `α₀` on a finite module with trivial action is bijective** for a
topological group `H` isomorphic to `G_K`, when the local field `K` contains a primitive `n`th
root of unity: for every finite discrete `H`-module `A` killed by `n` on which `H` acts trivially,
`H⁰(H, A) → Hom(H²(H, Hom(A, ℤ/n)), H²(H, ℤ/n))` is a bijection. This is the case `A = ℤ/n`
(`dualityMap0_zmod_bijective_of_isPrimitiveRoot` and its companions) propagated to every such `A`
by `TauCeti.ContCohomology.dualityMap0_bijective_of_smul_eq_self`. -/
theorem dualityMap0_bijective_of_isPrimitiveRoot :
    Function.Bijective (dualityMap0 H A (ZMod n)) :=
  dualityMap0_bijective_of_smul_eq_self htriv (AddEquiv.refl _) (h2ZModEquiv hζ φ htriv)
    (dualityMap0_zmod_bijective_of_isPrimitiveRoot hζ φ htriv)
    (dualityMap1_zmod_bijective_of_isPrimitiveRoot hζ φ htriv)
    (dualityMap2_zmod_bijective htriv).1 A hA hAtriv

/-- **Tate's duality map `α₁` on a finite module with trivial action is bijective** for a
topological group `H` isomorphic to `G_K`, when the local field `K` contains a primitive `n`th
root of unity: for every finite discrete `H`-module `A` killed by `n` on which `H` acts trivially,
`H¹(H, A) → Hom(H¹(H, Hom(A, ℤ/n)), H²(H, ℤ/n))` is a bijection. -/
theorem dualityMap1_bijective_of_isPrimitiveRoot :
    Function.Bijective (dualityMap1 H A (ZMod n)) :=
  have := finite_H1_zmod hζ φ htriv
  dualityMap1_bijective_of_smul_eq_self htriv (AddEquiv.refl _) (h2ZModEquiv hζ φ htriv)
    (dualityMap0_zmod_bijective_of_isPrimitiveRoot hζ φ htriv)
    (dualityMap1_zmod_bijective_of_isPrimitiveRoot hζ φ htriv)
    (dualityMap2_zmod_bijective htriv).1 A hA hAtriv

/-- **Tate's duality map `α₂` on a finite module with trivial action is bijective** for a
topological group `H` isomorphic to `G_K`, when the local field `K` contains a primitive `n`th
root of unity: for every finite discrete `H`-module `A` killed by `n` on which `H` acts trivially,
`H²(H, A) → Hom(H⁰(H, Hom(A, ℤ/n)), H²(H, ℤ/n))` is a bijection. -/
theorem dualityMap2_bijective_of_isPrimitiveRoot :
    Function.Bijective (dualityMap2 H A (ZMod n)) :=
  dualityMap2_bijective_of_smul_eq_self htriv (AddEquiv.refl _) (h2ZModEquiv hζ φ htriv)
    (dualityMap0_zmod_bijective_of_isPrimitiveRoot hζ φ htriv)
    (dualityMap1_zmod_bijective_of_isPrimitiveRoot hζ φ htriv)
    (dualityMap2_zmod_bijective htriv).1 A hA hAtriv

end TauCeti.ClassFieldTheory
