/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected

/-!
# Character maps read off the simple root subgroups

Let `F` be a homomorphism between the points of two Chevalley data of the same type over a
commutative ring `A`. Suppose that on the numbered positive and negative simple root subgroups

```text
F (x_{αᵢ}(u)) = x_{α_{σ i}}(cᵢ u ^ eᵢ),    F (x_{-αᵢ}(u)) = x_{-α_{σ i}}(cᵢ⁻¹ u ^ eᵢ)
```

for a node map `σ`, units `cᵢ` and exponents `eᵢ` with `(-1) ^ eᵢ = -1` in `A`. Then `F` carries
Steinberg's element `nᵢ(s) = x_{αᵢ}(s) x_{-αᵢ}(-s⁻¹) x_{αᵢ}(s)` to `n_{σ i}(cᵢ sᵉⁱ)`, hence the
simple coroot value `hᵢ(s) = nᵢ(s) nᵢ(1)⁻¹` to `h_{σ i}(sᵉⁱ)`. Since the full-weight torus
parameter `s` is the product of the `hᵢ(sᵢ)`, its image is the full-weight parameter whose
coordinate at `j` is `∏_{σ i = j} sᵢ ^ eᵢ`. Equivalently, `F` pulls characters back by any
endomorphism `φ` of the weight lattice `Fin t.rank → ℤ` with `(φ χ) i = eᵢ χ (σ i)`.

These are the computations by which the character map of a graph automorphism, a Frobenius map
or an exceptional isogeny is read from its values on the simple root subgroups. The condition on
`(-1) ^ eᵢ` holds for `eᵢ = 1` and for every power of the exponential characteristic of `A`. No
generation of the points by root subgroups is used: the statements concern the image of the
full-weight parametrization only, which is the whole actual torus for the full-weight datum.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.map_weylElement_eq_weylElement_mul_pow`: Steinberg's elements
  at the simple roots are carried to Steinberg's elements.
* `TauCeti.DynkinType.ChevalleyDatum.map_simpleCorootPoints_eq_simpleCorootPoints_pow`: the simple
  coroots are carried to simple coroots, with the parameter raised to the exponent.
* `ChevalleyDatum.map_torusPoints_fullWeightTorusRestriction_torusPointMap_of_rootSubgroupPoints`:
  the resulting equation on the full-weight torus parameters.
* `TauCeti.DynkinType.ChevalleyDatum.isCharacterMap_of_rootSubgroupPoints`: the character map of
  an endomorphism, on the full-weight parametrization of the torus.
* `TauCeti.DynkinType.isCharacterMap_scChevalleyDatum_of_rootSubgroupPoints`: the character map on
  the whole torus of the full-weight datum.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19, and Chapter 10,
  Theorems 28 and 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D E : ChevalleyDatum t ht) {A : Type v} [CommRing A]

/-- **Steinberg's element at a simple root is carried to Steinberg's element.** If a homomorphism
sends `x_{αᵢ}(u)` to `x_{αⱼ}(c u ^ e)` and `x_{-αᵢ}(u)` to `x_{-αⱼ}(c⁻¹ u ^ e)`, with
`(-1) ^ e = -1`, then it sends `nᵢ(s)` to `nⱼ(c sᵉ)`. -/
theorem map_weylElement_eq_weylElement_mul_pow (f : D.points A →* E.points A) {i j : Fin t.rank}
    (c : Aˣ) {e : ℕ} (he : (-1 : A) ^ e = -1)
    (hpos : ∀ u : A, f (D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints (t.simpleIndex ht j) A (Multiplicative.ofAdd (c * u ^ e)))
    (hneg : ∀ u : A, f (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) (t.simpleIndex ht i)) A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht j) (t.simpleIndex ht j)) A
          (Multiplicative.ofAdd (((c⁻¹ : Aˣ) : A) * u ^ e))) (s : Aˣ) :
    f (D.weylElement (t.simpleIndex ht i) A s) =
      E.weylElement (t.simpleIndex ht j) A (c * s ^ e) := by
  -- The middle parameter is odd in `s⁻¹`, because `(-1) ^ e = -1`.
  have hmid : ((c⁻¹ : Aˣ) : A) * (-((s⁻¹ : Aˣ) : A)) ^ e = -(((c * s ^ e)⁻¹ : Aˣ) : A) := by
    rw [neg_pow, he, mul_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [weylElement_def, weylElement_def, map_mul, map_mul, hpos, hneg, hmid, Units.val_mul,
    Units.val_pow_eq_pow_val]

/-- **The simple coroots are carried to simple coroots.** Under the hypotheses of
`TauCeti.DynkinType.ChevalleyDatum.map_weylElement_eq_weylElement_mul_pow`, the homomorphism sends
`hᵢ(s)` to `hⱼ(sᵉ)`; the unit `c` cancels. -/
theorem map_simpleCorootPoints_eq_simpleCorootPoints_pow (f : D.points A →* E.points A)
    {i j : Fin t.rank} (c : Aˣ) {e : ℕ} (he : (-1 : A) ^ e = -1)
    (hpos : ∀ u : A, f (D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints (t.simpleIndex ht j) A (Multiplicative.ofAdd (c * u ^ e)))
    (hneg : ∀ u : A, f (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) (t.simpleIndex ht i)) A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht j) (t.simpleIndex ht j)) A
          (Multiplicative.ofAdd (((c⁻¹ : Aˣ) : A) * u ^ e))) (s : Aˣ) :
    f (D.simpleCorootPoints i A s) = E.simpleCorootPoints j A (s ^ e) := by
  have hn := D.map_weylElement_eq_weylElement_mul_pow E f c he hpos hneg
  -- Since `hⱼ(a) = nⱼ(a) nⱼ(1)⁻¹`, the quotient `nⱼ(a) nⱼ(b)⁻¹` is the coroot value `hⱼ(a / b)`.
  have hw (a b : Aˣ) : E.weylElement (t.simpleIndex ht j) A a *
      (E.weylElement (t.simpleIndex ht j) A b)⁻¹ = E.simpleCorootPoints j A (a / b) := by
    rw [map_div, simpleCorootPoints_eq_weylElement_mul_inv,
      simpleCorootPoints_eq_weylElement_mul_inv]
    rw [div_eq_mul_inv]
    group
  rw [simpleCorootPoints_eq_weylElement_mul_inv, map_mul, map_inv, hn, hn, one_pow, mul_one, hw,
    mul_div_cancel_left]

variable {D E}

/-- **The full-weight torus equation of a homomorphism given on the simple root subgroups.** If a
homomorphism sends `x_{±αᵢ}(u)` to `x_{±α_{σ i}}(cᵢ^{±1} u ^ eᵢ)`, with `(-1) ^ eᵢ = -1`, then on
full-weight torus parameters it acts through any `φ` with `(φ χ) i = eᵢ χ (σ i)`; that is, the
coordinate of the image at `j` is `∏_{σ i = j} sᵢ ^ eᵢ`. -/
theorem map_torusPoints_fullWeightTorusRestriction_torusPointMap_of_rootSubgroupPoints
    (f : D.points A →* E.points A)
    (σ : Fin t.rank → Fin t.rank) (c : Fin t.rank → Aˣ) (e : Fin t.rank → ℕ)
    (he : ∀ i, (-1 : A) ^ e i = -1)
    (hpos : ∀ i (u : A), f (D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints (t.simpleIndex ht (σ i)) A (Multiplicative.ofAdd (c i * u ^ e i)))
    (hneg : ∀ i (u : A), f (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) (t.simpleIndex ht i)) A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht (σ i)) (t.simpleIndex ht (σ i))) A
          (Multiplicative.ofAdd (((c i)⁻¹ : Aˣ) * u ^ e i)))
    (φ : Module.End ℤ (Fin t.rank → ℤ)) (hφ : ∀ χ i, φ χ i = e i * χ (σ i))
    (s : Fin t.rank → Aˣ) :
    f (D.torusPoints A (D.fullWeightTorusRestriction A s)) =
      E.torusPoints A (E.fullWeightTorusRestriction A (torusPointMap φ s)) := by
  classical
  -- The image parameter is the product of the single coordinates `s i ^ e i` placed at `σ i`.
  have hparam : torusPointMap φ s = (List.ofFn fun i => Pi.mulSingle (σ i) (s i ^ e i)).prod := by
    rw [List.prod_ofFn]
    funext j
    rw [torusPointMap_apply, torusCharacter_def, Finset.prod_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hφ]
    by_cases h : σ i = j
    · rw [h, Pi.single_eq_same, Pi.mulSingle_eq_same, mul_one, zpow_natCast]
    · rw [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne (Ne.symm h), mul_zero, zpow_zero]
  rw [torusPoints_fullWeightTorusRestriction_eq_prod_simpleCorootPoints, map_list_prod,
    List.map_ofFn, hparam, ← MonoidHom.comp_apply, map_list_prod, List.map_ofFn]
  refine congrArg _ (congrArg _ (funext fun i => ?_))
  rw [Function.comp_apply, Function.comp_apply, MonoidHom.comp_apply,
    D.map_simpleCorootPoints_eq_simpleCorootPoints_pow E f (c i) (he i) (hpos i) (hneg i),
    simpleCorootPoints_eq_torusPoints, simpleCorootParameter_eq_fullWeightTorusRestriction]

/-- **The character map of an endomorphism given on the simple root subgroups.** If an
endomorphism of the points sends `x_{±αᵢ}(u)` to `x_{±α_{σ i}}(cᵢ^{±1} u ^ eᵢ)`, with
`(-1) ^ eᵢ = -1`, then on the full-weight parametrization of the torus it pulls characters back by
any `φ` with `(φ χ) i = eᵢ χ (σ i)`. -/
theorem isCharacterMap_of_rootSubgroupPoints (F : D.points A →* D.points A)
    (σ : Fin t.rank → Fin t.rank) (c : Fin t.rank → Aˣ) (e : Fin t.rank → ℕ)
    (he : ∀ i, (-1 : A) ^ e i = -1)
    (hpos : ∀ i (u : A), F (D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd u)) =
      D.rootSubgroupPoints (t.simpleIndex ht (σ i)) A (Multiplicative.ofAdd (c i * u ^ e i)))
    (hneg : ∀ i (u : A), F (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) (t.simpleIndex ht i)) A (Multiplicative.ofAdd u)) =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht (σ i)) (t.simpleIndex ht (σ i))) A
          (Multiplicative.ofAdd (((c i)⁻¹ : Aˣ) * u ^ e i)))
    (φ : Module.End ℤ (Fin t.rank → ℤ)) (hφ : ∀ χ i, φ χ i = e i * χ (σ i)) :
    IsCharacterMap ((D.torusPoints A).comp (D.fullWeightTorusRestriction A)) F φ :=
  isCharacterMap_iff.mpr fun s =>
    map_torusPoints_fullWeightTorusRestriction_torusPointMap_of_rootSubgroupPoints F σ c e he hpos
      hneg φ hφ s

end

end TauCeti.DynkinType.ChevalleyDatum

namespace TauCeti.DynkinType

open ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} {A : Type v} [CommRing A]

/-- **The character map on `G_sc(t)` of an endomorphism given on the simple root subgroups.** If
an endomorphism of the points of `G_sc(t)` sends `x_{±αᵢ}(u)` to `x_{±α_{σ i}}(cᵢ^{±1} u ^ eᵢ)`,
with `(-1) ^ eᵢ = -1`, then it pulls characters of the whole torus back by any `φ` with
`(φ χ) i = eᵢ χ (σ i)`. -/
theorem isCharacterMap_scChevalleyDatum_of_rootSubgroupPoints
    (F : (t.scChevalleyDatum ht).points A →* (t.scChevalleyDatum ht).points A)
    (σ : Fin t.rank → Fin t.rank) (c : Fin t.rank → Aˣ) (e : Fin t.rank → ℕ)
    (he : ∀ i, (-1 : A) ^ e i = -1)
    (hpos : ∀ i (u : A), F ((t.scChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht i) A
        (Multiplicative.ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht (σ i)) A
        (Multiplicative.ofAdd (c i * u ^ e i)))
    (hneg : ∀ i (u : A), F ((t.scChevalleyDatum ht).rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i))
        A (Multiplicative.ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht (σ i)) (t.simpleIndex ht (σ i))) A
          (Multiplicative.ofAdd (((c i)⁻¹ : Aˣ) * u ^ e i)))
    (φ : Module.End ℤ (Fin t.rank → ℤ)) (hφ : ∀ χ i, φ χ i = e i * χ (σ i)) :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A) F φ :=
  isCharacterMap_iff.mpr fun s => by
    simpa only [MonoidHom.comp_apply, scChevalleyDatum_fullWeightTorusRestriction] using
      (isCharacterMap_of_rootSubgroupPoints F σ c e he hpos hneg φ hφ).map_apply s

end TauCeti.DynkinType
