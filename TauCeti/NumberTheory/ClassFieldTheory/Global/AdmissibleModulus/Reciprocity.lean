/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Ramification
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient

/-!
# Ray-class reciprocity

Let `L/K` be a finite abelian extension of number fields and `𝔪` a modulus of `K` admissible for
`L/K`. The ray class group `Cl_𝔪` is the quotient of the idele class group `C_K` by the ray
subgroup of `𝔪` (`GlobalNumberFields.rayClassQuotient`, with kernel
`GlobalNumberFields.ker_rayClassQuotient`), and admissibility says that the ray subgroup lies in
the norm group `N_{L/K}(C_L)`, the kernel of the global Artin map. So the global Artin map
factors through `Cl_𝔪`: this is the **ray-class Artin map**

`rayClassArtinMap 𝔪 h : Cl_𝔪 →* Gal(L/K)`,

read in `Gal(L/K)` itself, which is its own abelianization. Its idelic characterization is
`of_rayClassArtinMap_rayClassQuotient`. The admissibility proof `h` is an argument of the
definition: for an inadmissible modulus the global Artin map need not factor, as for `ℚ(i)/ℚ` and
the trivial modulus (`not_isAdmissibleModulus_one_Qi`).

The map is surjective (`rayClassArtinMap_surjective`), because the global Artin map is, and its
kernel is the image of the norm group in `Cl_𝔪` (`ker_rayClassArtinMap`).

On ideals it is the ideal-theoretic Artin map. The prime idele class at a finite place `v` outside
the support of `𝔪` is congruent to one modulo `𝔪`, and its ray class is the ray class of the prime
`v` (`rayClassQuotient_primeIdeleClass`). An admissible modulus contains every ramified prime in
its support (`IsAdmissibleModulus.isUnramifiedAway`), and the global Artin symbol of the prime
idele class at an unramified place is the Frobenius there (`globalArtinMap_ideal`). Since the
ideal-theoretic Artin map is determined by its values on primes, the ray-class Artin map,
composed with the ray class of an ideal prime to `𝔪`, is
`NumberFieldArithmetic.artinHomAway` for the excluded set `𝔪.support`
(`rayClassArtinMap_comp_rayClassMk`). This is the **splitting law**: the ray-class Artin symbol
of a prime ideal `𝔭` prime to `𝔪` is an arithmetic Frobenius at every prime of `L` above `𝔭`
(`isArithFrobAt_rayClassArtinMap_idealClass`), and its conjugacy class is the Artin symbol of `𝔭`
(`rayClassArtinMap_idealClass`).

## Main definitions

* `TauCeti.ClassFieldTheory.rayClassArtinMap`: the ray-class Artin map
  `Cl_𝔪 →* Gal(L/K)` of an admissible modulus.

## Main results

* `TauCeti.ClassFieldTheory.of_rayClassArtinMap_rayClassQuotient`: the ray-class Artin map is the
  factorization of the global Artin map through the ray class group.
* `TauCeti.ClassFieldTheory.rayClassArtinMap_surjective`: the ray-class Artin map is surjective.
* `TauCeti.ClassFieldTheory.ker_rayClassArtinMap`: its kernel is the image of the norm group.
* `TauCeti.ClassFieldTheory.rayClassQuotient_primeIdeleClass`: the ray class of the prime idele
  class at a place outside the support of `𝔪` is the ray class of the prime.
* `TauCeti.ClassFieldTheory.rayClassArtinMap_comp_rayClassMk`,
  `TauCeti.ClassFieldTheory.rayClassArtinMap_rayClassMk`: on the ideals prime to `𝔪` the
  ray-class Artin map is the ideal-theoretic Artin map.
* `TauCeti.ClassFieldTheory.isArithFrobAt_rayClassArtinMap_idealClass`,
  `TauCeti.ClassFieldTheory.rayClassArtinMap_idealClass`: the splitting law.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7 (the Artin reciprocity law for ray class
  groups, Theorem 7.1).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3 and Chapter VII, §5.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

/-! ### The ray class of a prime idele class -/

section PrimeIdeleClass

variable {K : Type} [Field K] [NumberField K]

/-- **The ray class of a prime idele class is the ray class of the prime.** For a finite place `v`
of `K` outside the support of a modulus `𝔪`, the prime idele class at `v` has the ray class of the
prime `v`: the idele with a uniformizer at `v` and `1` elsewhere is congruent to one modulo `𝔪`,
and its fractional ideal is `v`. -/
theorem rayClassQuotient_primeIdeleClass {𝔪 : Modulus K} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ 𝔪.support) (I : idealsPrimeTo 𝔪)
    (hI : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) :
    rayClassQuotient 𝔪 (primeIdeleClass K v) = rayClassMk 𝔪 I := by
  obtain ⟨π, hπ, h⟩ := exists_isUniformizer_primeIdeleClass_eq K v
  -- The idele concentrated at `v` is trivial at the places of `𝔪`.
  have hmem : IdeleGroup.ofAdicCompletion (𝓞 K) K v π ∈ ideleCongrOneSubgroup 𝔪 := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun v' hv' ↦ ?_, fun w _ ↦ ?_⟩
    · have hne : v' ≠ v := fun he ↦ hv ((Modulus.mem_support_iff 𝔪 v).mpr (he ▸ hv'))
      simp [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne v' hne]
    · simp [InfinitePlace.ideleInfiniteCoord_ofAdicCompletion]
  -- A uniformizer has valuation `exp (-1)`, so the fractional ideal of the idele is `v`.
  have hval : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1) := by
    have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    have h1 := TauCeti.normalizedValuationWithZero_coe π
    rw [HeightOneSpectrum.normalizedValuationWithZero_adicCompletion,
      (isUniformizer_def π).1 hπ] at h1
    rw [← inv_inv (Valued.v (π : v.adicCompletion K)), h1, ← WithZero.exp_eq_coe_ofAdd,
      WithZero.exp_neg]
  rw [h, IdeleClassGroup.ofAdicCompletion_apply, rayClassQuotient_mk_of_mem hmem]
  refine congrArg _ (Subtype.ext (Units.ext ?_))
  dsimp only
  rw [HeightOneSpectrum.toFractionalIdeal_toFiniteIdele_ofAdicCompletion, hval, WithZero.log_exp,
    neg_neg, zpow_one, HeightOneSpectrum.coe_unitOfPrime, hI]

end PrimeIdeleClass

/-! ### The ray-class Artin map -/

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

/-- The global Artin map of an abelian extension, read in the Galois group itself. -/
private def ideleClassArtinMap : IdeleClassGroup (𝓞 K) K →* Gal(L/K) :=
  (Abelianization.lift (MonoidHom.id Gal(L/K))).comp
    (MonoidHom.toAdditive.symm (globalArtinMap K L IsSepClosed.lift))

private theorem ideleClassArtinMap_apply (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassArtinMap K L c =
      Abelianization.lift (MonoidHom.id Gal(L/K))
        (globalArtinMap K L IsSepClosed.lift (.ofMul c)).toMul :=
  (rfl)

private theorem of_ideleClassArtinMap (ι : L →ₐ[K] SeparableClosure K)
    (c : IdeleClassGroup (𝓞 K) K) :
    Abelianization.of (ideleClassArtinMap K L c) = (globalArtinMap K L ι (.ofMul c)).toMul := by
  -- `Gal(L/K)` is commutative, so `Abelianization.of` inverts the lift of the identity.
  have hof : Abelianization.of.comp (Abelianization.lift (MonoidHom.id Gal(L/K))) =
      MonoidHom.id _ :=
    Abelianization.hom_ext _ _ rfl
  rw [ideleClassArtinMap_apply, ← MonoidHom.comp_apply, hof, MonoidHom.id_apply,
    globalArtinMap_eq_of_iota K L ι IsSepClosed.lift]

private theorem ker_ideleClassArtinMap :
    (ideleClassArtinMap K L).ker =
      (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  ext c
  have hof : Function.Injective (Abelianization.of (G := Gal(L/K))) :=
    Function.LeftInverse.injective (g := Abelianization.lift (MonoidHom.id _))
      fun σ ↦ Abelianization.lift_apply_of _ σ
  rw [MonoidHom.mem_ker, ← globalArtinMap_eq_zero_iff K L IsSepClosed.lift, ← hof.eq_iff,
    of_ideleClassArtinMap K L IsSepClosed.lift, map_one, ← toMul_zero,
    Additive.toMul.injective.eq_iff]

variable {K L}

/-- **The ray-class Artin map** `Cl_𝔪 →* Gal(L/K)` of a finite abelian extension `L/K` of number
fields and a modulus `𝔪` admissible for `L/K`: the factorization of the global Artin map through
the ray class group of `𝔪`, which exists because admissibility puts the ray subgroup inside the
norm group, the kernel of the global Artin map. It is characterized by
`of_rayClassArtinMap_rayClassQuotient`, and on ideals it is the ideal-theoretic Artin map
(`rayClassArtinMap_comp_rayClassMk`). -/
def rayClassArtinMap (𝔪 : Modulus K) (h : IsAdmissibleModulus K L 𝔪) :
    RayClassGroup 𝔪 →* Gal(L/K) :=
  (rayClassQuotient 𝔪).liftOfSurjective (rayClassQuotient_surjective 𝔪)
    ⟨ideleClassArtinMap K L, by
      rw [ker_rayClassQuotient, ker_ideleClassArtinMap]
      exact isAdmissibleModulus_iff.1 h⟩

variable {𝔪 : Modulus K} (h : IsAdmissibleModulus K L 𝔪)

/-- **The ray-class Artin map factors the global Artin map**: the class in `Gal(L/K)^ab` of the
ray-class Artin symbol of the ray class of `c ∈ C_K` is the global Artin symbol of `c`, for every
embedding `ι` of `L` into the separable closure. -/
theorem of_rayClassArtinMap_rayClassQuotient (ι : L →ₐ[K] SeparableClosure K)
    (c : IdeleClassGroup (𝓞 K) K) :
    Abelianization.of (rayClassArtinMap 𝔪 h (rayClassQuotient 𝔪 c)) =
      (globalArtinMap K L ι (.ofMul c)).toMul := by
  rw [rayClassArtinMap, MonoidHom.liftOfRightInverse_comp_apply, of_ideleClassArtinMap K L ι]

/-- **Ray-class reciprocity is surjective**: every automorphism of `L/K` is the ray-class Artin
symbol of a ray class of `𝔪`. -/
theorem rayClassArtinMap_surjective : Function.Surjective (rayClassArtinMap 𝔪 h) := by
  intro σ
  obtain ⟨c, hc⟩ := surjective_globalArtinMap K L IsSepClosed.lift (.ofMul (Abelianization.of σ))
  refine ⟨rayClassQuotient 𝔪 c.toMul, ?_⟩
  rw [rayClassArtinMap, MonoidHom.liftOfRightInverse_comp_apply, ideleClassArtinMap_apply,
    ofMul_toMul, hc, toMul_ofMul, Abelianization.lift_apply_of, MonoidHom.id_apply]

/-- **The kernel of ray-class reciprocity** is the image in the ray class group of `𝔪` of the
idele-class norm group `N_{L/K}(C_L)`. -/
theorem ker_rayClassArtinMap :
    (rayClassArtinMap 𝔪 h).ker =
      (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.map
        (rayClassQuotient 𝔪) := by
  have hcomp : (rayClassArtinMap 𝔪 h).comp (rayClassQuotient 𝔪) = ideleClassArtinMap K L :=
    MonoidHom.liftOfRightInverse_comp _ _ _ _
  rw [← ker_ideleClassArtinMap, ← hcomp, ← MonoidHom.comap_ker,
    Subgroup.map_comap_eq_self_of_surjective (rayClassQuotient_surjective 𝔪)]

/-! ### The splitting law -/

/-- **On ideals, ray-class reciprocity is the ideal-theoretic Artin map**: the ray-class Artin
symbol of the ray class of an invertible fractional ideal prime to `𝔪` is the value of
`NumberFieldArithmetic.artinHomAway` at that ideal, for the excluded set `𝔪.support`, outside
which `L/K` is unramified (`IsAdmissibleModulus.isUnramifiedAway`). -/
theorem rayClassArtinMap_comp_rayClassMk :
    (rayClassArtinMap 𝔪 h).comp (rayClassMk 𝔪) =
      NumberFieldArithmetic.artinHomAway algEquiv_commute_of_isAbelianGalois 𝔪.support
        h.isUnramifiedAway := by
  refine eq_artinHomAway_of_globalArtinMap L IsSepClosed.lift 𝔪.support h.isUnramifiedAway _
    fun I v hv hI ↦ ?_
  rw [MonoidHom.comp_apply, ← rayClassQuotient_primeIdeleClass hv I hI,
    of_rayClassArtinMap_rayClassQuotient h IsSepClosed.lift, ofMul_toMul]

/-- **On ideals, ray-class reciprocity is the ideal-theoretic Artin map**, pointwise. -/
@[simp]
theorem rayClassArtinMap_rayClassMk (I : idealsPrimeTo 𝔪) :
    rayClassArtinMap 𝔪 h (rayClassMk 𝔪 I) =
      NumberFieldArithmetic.artinHomAway algEquiv_commute_of_isAbelianGalois 𝔪.support
        h.isUnramifiedAway I := by
  rw [← MonoidHom.comp_apply, rayClassArtinMap_comp_rayClassMk]

/-- **The splitting law**: the ray-class Artin symbol of the ray class of a prime ideal `𝔭` of `K`
prime to `𝔪` is an arithmetic Frobenius at every prime of `L` above `𝔭`. -/
theorem isArithFrobAt_rayClassArtinMap_idealClass (I : integralIdealsPrimeTo 𝔪)
    [(I : Ideal (𝓞 K)).IsMaximal] (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (I : Ideal (𝓞 K))] :
    IsArithFrobAt (𝓞 K) (rayClassArtinMap 𝔪 h (idealClass 𝔪 I)) Q := by
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := (Modulus.isCoprimeTo_iff.mp
    (Modulus.mem_integralIdealsPrimeTo.mp I.2)).1
  let v : HeightOneSpectrum (𝓞 K) := ⟨I, inferInstance, hI⟩
  have hv : v ∉ 𝔪.support := fun hv ↦
    (Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp I.2)).2 v hv dvd_rfl
  have : Q.LiesOver v.asIdeal := ‹Q.LiesOver (I : Ideal (𝓞 K))›
  rw [idealClass_apply, rayClassArtinMap_rayClassMk,
    NumberFieldArithmetic.artinHomAway_apply_eq_artinElementAway _ _ _ _ v
      (NumberFieldArithmetic.coe_integralIdealsAwayHom 𝔪.support I)]
  exact NumberFieldArithmetic.isArithFrobAt_artinElementAway _ _ _ hv Q

/-- **The splitting law, through the Artin symbol**: the conjugacy class of the ray-class Artin
symbol of the ray class of a prime ideal `𝔭` of `K` prime to `𝔪` is the Artin symbol of `𝔭`. -/
theorem rayClassArtinMap_idealClass (I : integralIdealsPrimeTo 𝔪) [(I : Ideal (𝓞 K)).IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (I : Ideal (𝓞 K))],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ConjClasses.mk (rayClassArtinMap 𝔪 h (idealClass 𝔪 I)) =
      artinSymbol (L := L) (I : Ideal (𝓞 K)) hur := by
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty ((I : Ideal (𝓞 K)).primesOver (𝓞 L)))
  exact (artinSymbol_eq_mk_of_isArithFrobAt _ hur Q _
    (isArithFrobAt_rayClassArtinMap_idealClass h I Q)).symm

end TauCeti.ClassFieldTheory
