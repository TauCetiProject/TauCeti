/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Character
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Representability
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
import TauCeti.Algebra.TensorProduct.MapLinear

/-!
# The centralizer of a diagonalizable subgroup

Let `G = Spec H` be an affine group scheme over a commutative ring `R` and let `D(X) → G` be a
closed diagonalizable subgroup, given by a surjective morphism `π : H →ₐc[R] R[X]` of
coordinate Hopf algebras for a commutative group `X` of characters. This file constructs the
centralizer `Z_G(D(X))` as a closed subgroup scheme of `G`, that is, as a Hopf ideal of `H`.

The defining equations are the coefficients, in the basis of `R[X]` indexed by characters, of
the **conjugation defect** of a coordinate `x`: the difference between the universal conjugate of
the universal point of `D(X)` by the universal point of `G` and that point itself, written in the
coordinates `H ⊗[R] R[X]`. A point of `G` with values in an algebra `A` kills these coefficients
exactly when it commutes with every point of `D(X)` after every extension of `A`; since such
points form a subgroup, the coefficient ideal is a Hopf ideal. The construction needs no basis of
`H`, only the canonical basis of the monoid algebra `R[X]`, and no hypothesis on `R`.

The rational points of the centralizer are the rational points of `G` whose conjugation fixes
the coordinate map `π`. Every such point normalizes `D(X)`, and, when the base has connected prime
spectrum, the rational points of the centralizer are exactly the normalizing points acting
trivially on the character group `X`, that is, the kernel of
`BialgHom.normalizerCharacterHom`.

Since `D(X)` is commutative, it lies in its own centralizer; and the centralizer is the whole
group exactly when `D(X)` is a central closed subgroup of `G`.

A homomorphism `D(Y) → D(X)` with coordinate map `ψ : R[X] → R[Y]` makes `ψ ∘ π` the coordinate
map of the composite `D(Y) → D(X) → G`. The centralizer of this composite contains that of `D(X)`,
and contains `D(X)` itself. The main instance is the common kernel `D(X ⧸ S) → D(X)` of a subgroup
`S` of characters, with `ψ` induced by the quotient map.

## Main declarations

* `BialgHom.centralizerDefect`: the conjugation defect of a coordinate, in `H ⊗[R] R[X]`.
* `BialgHom.centralizerCoefficient`: its coefficient at a character; `centralizerDefect_def`
  and `centralizerCoefficient_def` are the public formulas for these two definitions.
* `BialgHom.centralizerHopfIdeal`: the Hopf ideal cutting out the centralizer of the diagonalizable
  subgroup.
* `BialgHom.centralizerHopfIdeal_le_ker_iff`: an algebra-valued point kills the centralizer
  ideal exactly when it commutes with every point of the diagonalizable subgroup over every
  extension of its value algebra.
* `BialgHom.mem_centralizerPointsSubgroup_iff`: the same statement for the subgroup of points cut
  out by the centralizer ideal.
* `BialgHom.centralizerHopfIdeal_le_ker_iff_comp_pointConjugationAlgHom_eq`: a rational point
  lies in the centralizer exactly when conjugation by it fixes the coordinate map `π`.
* `BialgHom.normalizerCharacterHom_eq_one_iff_centralizerHopfIdeal_le_ker`: the rational points of
  the centralizer are the kernel of the normalizer action on characters.
* `BialgHom.centralizerHopfIdeal_le_kerOfSurjective`: the diagonalizable subgroup lies in its own
  centralizer.
* `BialgHom.centralizerHopfIdeal_eq_bot_iff_isCentral`: the centralizer is the whole group exactly
  when the diagonalizable subgroup is central.
* `BialgHom.centralizerHopfIdeal_comp_le`: the centralizer of a composite `D(Y) → D(X) → G`
  contains the centralizer of `D(X)`.
* `BialgHom.centralizerHopfIdeal_mapDomainBialgHom_comp_eq_of_leftInverse`: a split injection
  of character groups preserves the centralizer.
* `BialgHom.centralizerHopfIdeal_comp_le_kerOfSurjective`: the centralizer of a composite
  `D(Y) → D(X) → G` contains `D(X)`.
* `BialgHom.centralizerHopfIdeal_mapDomainBialgHom_mk'_comp_anti`: the centralizer of the common
  kernel `D(X ⧸ S)` of a subgroup `S` of characters grows with `S`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 1 (normalizers and centralizers), §12
  (diagonalizable groups) and §13 (tori acting on schemes).
* SGA 3, Exposé VI_B, Corollaire 6.2.5 (i), and Exposé XI, Corollaire 5.3.
-/

public section

open TensorProduct WithConv

namespace BialgHom

open TauCeti

universe u v w x y

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X)

/-! ## The conjugation defect and its coefficients -/

/-- The conjugation defect of a coordinate `x`: in the coordinates `H ⊗[R] R[X]` of `G × D(X)`,
the difference between the conjugate of the universal point of `D(X)` by the universal point of
`G` and the universal point of `D(X)` itself. The first tensor factor is the conjugating variable
of `G`, the second the conjugated variable of `D(X)`. -/
noncomputable def centralizerDefect (x : H) : H ⊗[R] MonoidAlgebra R X :=
  Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom
      (HopfAlgebra.conjugationAlgHom (R := R) (H := H) x) -
    1 ⊗ₜ[R] π x

/-- The defining formula of the conjugation defect. This is the public interface to the
definition, whose body is not exposed outside this module. -/
theorem centralizerDefect_def (x : H) :
    centralizerDefect π x =
      Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H) x) -
        1 ⊗ₜ[R] π x := by
  rfl

/-- The coefficient of the conjugation defect of `x` at the character `χ`, in the canonical basis
of `R[X]`. These coefficients generate the centralizer ideal. -/
noncomputable def centralizerCoefficient (x : H) (χ : X) : H :=
  LinearMap.tensorComponent (Comodule.monoidCoeff R X χ) (centralizerDefect π x)

/-- The defining formula of a coefficient of the conjugation defect. This is the public interface
to the definition, whose body is not exposed outside this module. -/
theorem centralizerCoefficient_def (x : H) (χ : X) :
    centralizerCoefficient π x χ =
      LinearMap.tensorComponent (Comodule.monoidCoeff R X χ) (centralizerDefect π x) := by
  rfl

/-- A linear map out of `H` kills every coefficient of a conjugation defect exactly when it kills
the defect itself, after tensoring with the identity of `R[X]`. -/
theorem map_centralizerDefect_eq_zero_iff {A : Type x} [AddCommMonoid A] [Module R A]
    (f : H →ₗ[R] A) (x : H) :
    TensorProduct.map f LinearMap.id (centralizerDefect π x) = 0 ↔
      ∀ χ, f (centralizerCoefficient π x χ) = 0 := by
  constructor
  · intro h χ
    have hχ := congrArg (LinearMap.tensorComponent (Comodule.monoidCoeff R X χ)) h
    rwa [LinearMap.tensorComponent_map, LinearMap.comp_id, map_zero] at hχ
  · intro h
    apply (Comodule.tensorCoeffEquiv R X A).injective
    ext χ
    rw [Comodule.tensorCoeffEquiv_apply, map_zero, Finsupp.zero_apply,
      LinearMap.tensorComponent_map, LinearMap.comp_id]
    exact h χ

/-- The ideal generated by all coefficients of all conjugation defects. -/
private noncomputable def centralizerIdeal : Ideal H :=
  Ideal.span (Set.range fun p : H × X ↦ centralizerCoefficient π p.1 p.2)

/-- A point kills the coefficient ideal exactly when it kills every conjugation defect. -/
private theorem centralizerIdeal_le_ker_iff {A : Type x} [CommRing A] [Algebra R A]
    (g : H →ₐ[R] A) :
    centralizerIdeal π ≤ RingHom.ker g ↔
      ∀ x, Algebra.TensorProduct.map g (AlgHom.id R (MonoidAlgebra R X))
        (centralizerDefect π x) = 0 := by
  rw [centralizerIdeal, Ideal.span_le]
  simp only [Set.range_subset_iff, Prod.forall, SetLike.mem_coe, RingHom.mem_ker]
  refine forall_congr' fun x ↦ ?_
  rw [Algebra.TensorProduct.map_apply_eq_map, AlgHom.toLinearMap_id,
    map_centralizerDefect_eq_zero_iff]
  simp only [AlgHom.toLinearMap_apply]

/-- Evaluating the conjugation defect at a point `g` of `G` and then along an algebra map `ψ` out
of the tensor square computes `g' t g'⁻¹ - t`, where `g'` is `g` pushed along `ψ` and `t` is the
point of `D(X)` carried by `ψ`. -/
theorem apply_map_centralizerDefect {A : Type x} {B : Type y} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (g : WithConv (H →ₐ[R] A))
    (ψ : A ⊗[R] MonoidAlgebra R X →ₐ[R] B) (x : H) :
    ψ (Algebra.TensorProduct.map g.ofConv (AlgHom.id R (MonoidAlgebra R X))
        (centralizerDefect π x)) =
      (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g *
          BialgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight)) *
          (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g)⁻¹).ofConv x -
        (BialgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))).ofConv x := by
  have hcomp : (ψ.comp (Algebra.TensorProduct.map g.ofConv (AlgHom.id R (MonoidAlgebra R X)))).comp
      (Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom) =
      Algebra.TensorProduct.productMap
        (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g).ofConv
        (BialgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))).ofConv := by
    refine Algebra.TensorProduct.ext ?_ ?_ <;> ext h <;>
      simp [AlgHom.mapValue_apply, BialgHom.mapDomain_apply, ← Algebra.TensorProduct.one_def]
  rw [centralizerDefect, map_sub, map_sub, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp,
    ← AlgHom.comp_apply, HopfAlgebra.productMap_comp_conjugationAlgHom]
  congr 1
  simp [BialgHom.mapDomain_apply]

/-! ## The centralizer as a closed subgroup scheme -/

/-- The points of `G` killing the centralizer ideal are detected by commutation with the point of
`D(X)` carried by any injective algebra map `ψ` out of `A ⊗[R] R[X]`. -/
private theorem centralizerIdeal_le_ker_iff_commute_of_injective {A : Type x} {B : Type y}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (g : WithConv (H →ₐ[R] A))
    (ψ : A ⊗[R] MonoidAlgebra R X →ₐ[R] B) (hψ : Function.Injective ψ) :
    centralizerIdeal π ≤ RingHom.ker g.ofConv ↔
      Commute (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g)
        (BialgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))) := by
  rw [centralizerIdeal_le_ker_iff, commute_iff_eq, ← mul_inv_eq_iff_eq_mul]
  simp_rw [← map_eq_zero_iff ψ hψ, apply_map_centralizerDefect, sub_eq_zero]
  exact ⟨fun h ↦ ofConv_injective (AlgHom.ext h), fun h x ↦ by rw [h]⟩

/-- **The centralizer of a diagonalizable subgroup, as a Hopf ideal.** Its quotient represents
the points of `G` commuting with every point of `D(X)`. The ideal is generated by the coefficients
of the conjugation defects; it is a Hopf ideal because the points killing it form a subgroup
over every value algebra. -/
noncomputable def centralizerHopfIdeal : HopfIdeal R H :=
  HopfIdeal.ofIdealOfPointsSubgroup (centralizerIdeal π)
    (fun A ↦ (Subgroup.centralizer
        {BialgHom.mapDomain π (toConv (Algebra.TensorProduct.includeRight :
          MonoidAlgebra R X →ₐ[R] A ⊗[R] MonoidAlgebra R X))}).comap
      (AlgHom.mapValue (H := H) (Algebra.TensorProduct.includeLeft (R := R) (S := R))))
    fun A g ↦ by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← commute_iff_eq,
        centralizerIdeal_le_ker_iff_commute_of_injective π g (AlgHom.id R _)
          Function.injective_id]
      simp only [AlgHom.id_comp]

/-- The centralizer ideal is generated by the coefficients of the conjugation defects. -/
theorem centralizerHopfIdeal_toIdeal :
    (centralizerHopfIdeal π).toIdeal =
      Ideal.span (Set.range fun p : H × X ↦ centralizerCoefficient π p.1 p.2) :=
  HopfIdeal.ofIdealOfPointsSubgroup_toIdeal _ _ _

/-- A point of `G` kills the centralizer ideal exactly when it commutes with the point of `D(X)`
carried by any injective algebra map `ψ` out of `A ⊗[R] R[X]`. The identity of `A ⊗[R] R[X]`
carries the universal point of `D(X)`; the left unitor `R ⊗[R] R[X] ≃ R[X]` is used for rational
points. -/
theorem centralizerHopfIdeal_le_ker_iff_commute_of_injective {A : Type x} {B : Type y}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (g : WithConv (H →ₐ[R] A))
    (ψ : A ⊗[R] MonoidAlgebra R X →ₐ[R] B) (hψ : Function.Injective ψ) :
    (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv ↔
      Commute (AlgHom.mapValue (ψ.comp Algebra.TensorProduct.includeLeft) g)
        (BialgHom.mapDomain π (toConv (ψ.comp Algebra.TensorProduct.includeRight))) := by
  rw [centralizerHopfIdeal_toIdeal]
  exact centralizerIdeal_le_ker_iff_commute_of_injective π g ψ hψ

/-- A point of `G` killing the centralizer ideal commutes with every point of `D(X)` over every
extension of its value algebra. -/
theorem commute_mapValue_mapDomain_of_centralizerHopfIdeal_le_ker {A : Type x} {B : Type y}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] {g : WithConv (H →ₐ[R] A)}
    (hg : (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv) (φ : A →ₐ[R] B)
    (t : WithConv (MonoidAlgebra R X →ₐ[R] B)) :
    Commute (AlgHom.mapValue φ g) (BialgHom.mapDomain π t) := by
  have h := ((centralizerHopfIdeal_le_ker_iff_commute_of_injective π g (AlgHom.id _ _)
    Function.injective_id).mp hg).map
    (AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap φ t.ofConv))
  have hleft : AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap φ t.ofConv)
      (AlgHom.mapValue ((AlgHom.id R _).comp Algebra.TensorProduct.includeLeft) g) =
      AlgHom.mapValue φ g := by
    apply ofConv_injective
    ext x
    simp [AlgHom.mapValue_apply]
  have hright : AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap φ t.ofConv)
      (BialgHom.mapDomain π (toConv ((AlgHom.id R _).comp Algebra.TensorProduct.includeRight))) =
      BialgHom.mapDomain π t := by
    apply ofConv_injective
    ext x
    simp [AlgHom.mapValue_apply, BialgHom.mapDomain_apply]
  rwa [hleft, hright] at h

/-- **A point of `G` kills the centralizer ideal exactly when it commutes with every point of
`D(X)` over every extension of its value algebra.** Quantifying over extensions is what makes
the condition functorial: the universal extension `A ⊗[R] R[X]` carries the universal point of
`D(X)`. -/
theorem centralizerHopfIdeal_le_ker_iff {A : Type x} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) :
    (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv ↔
      ∀ ⦃B : Type (max u w x)⦄ [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
        (t : WithConv (MonoidAlgebra R X →ₐ[R] B)),
        Commute (AlgHom.mapValue φ g) (BialgHom.mapDomain π t) := by
  constructor
  · intro hg B _ _ φ t
    exact commute_mapValue_mapDomain_of_centralizerHopfIdeal_le_ker π hg φ t
  · intro h
    have hu := h (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] MonoidAlgebra R X)
      (toConv (Algebra.TensorProduct.includeRight :
        MonoidAlgebra R X →ₐ[R] A ⊗[R] MonoidAlgebra R X))
    rw [centralizerHopfIdeal_le_ker_iff_commute_of_injective π g (AlgHom.id R _)
      Function.injective_id, AlgHom.id_comp, AlgHom.id_comp]
    exact hu

/-- The subgroup of `A`-valued points of `G` cut out by the centralizer ideal. -/
noncomputable abbrev centralizerPointsSubgroup (A : CommAlgCat.{x} R) :
    Subgroup (WithConv (H →ₐ[R] A)) :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of R H) (centralizerHopfIdeal π) A

/-- The points of the centralizer are the points of `G` commuting with every point of `D(X)`
over every extension of the value algebra. -/
theorem mem_centralizerPointsSubgroup_iff (A : CommAlgCat.{x} R) (g : WithConv (H →ₐ[R] A)) :
    g ∈ centralizerPointsSubgroup π A ↔
      ∀ ⦃B : Type (max u w x)⦄ [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
        (t : WithConv (MonoidAlgebra R X →ₐ[R] B)),
        Commute (AlgHom.mapValue φ g) (BialgHom.mapDomain π t) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, ← centralizerHopfIdeal_le_ker_iff]
  exact ⟨fun h x hx ↦ RingHom.mem_ker.mpr (h x (HopfIdeal.mem_toIdeal.mp hx)),
    fun h x hx ↦ RingHom.mem_ker.mp (h (HopfIdeal.mem_toIdeal.mpr hx))⟩

/-! ## Rational points -/

/-- **A rational point lies in the centralizer exactly when conjugation by it fixes the
coordinate map of the diagonalizable subgroup.** -/
theorem centralizerHopfIdeal_le_ker_iff_comp_pointConjugationAlgHom_eq
    (g : WithConv (H →ₐ[R] R)) :
    (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv ↔
      π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g) = π.toAlgHom := by
  rw [centralizerHopfIdeal_le_ker_iff_commute_of_injective π g
    (Algebra.TensorProduct.lid R (MonoidAlgebra R X)).toAlgHom
    (Algebra.TensorProduct.lid R (MonoidAlgebra R X)).injective]
  have hleft : AlgHom.mapValue (H := H)
      ((Algebra.TensorProduct.lid R (MonoidAlgebra R X)).toAlgHom.comp
        Algebra.TensorProduct.includeLeft) g =
      AlgHom.mapValue (Algebra.ofId R (MonoidAlgebra R X)) g := by
    apply ofConv_injective
    ext x
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lid_tmul,
      Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
  have hright : BialgHom.mapDomain π (toConv
      ((Algebra.TensorProduct.lid R (MonoidAlgebra R X)).toAlgHom.comp
        Algebra.TensorProduct.includeRight)) = toConv π.toAlgHom := by
    apply ofConv_injective
    ext x
    simp [BialgHom.mapDomain_apply]
  have hconj := HopfAlgebra.comp_pointConjugationAlgHom g (toConv π.toAlgHom)
  rw [ofConv_toConv] at hconj
  rw [hleft, hright, ← toConv_injective.eq_iff, hconj, commute_iff_eq, ← mul_inv_eq_iff_eq_mul]

/-- Conjugation by the inverse of a rational point fixes the coordinate map as soon as
conjugation by the point does. -/
private theorem comp_pointConjugationAlgHom_inv_eq_of_comp_eq {g : WithConv (H →ₐ[R] R)}
    (hg : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g) = π.toAlgHom) :
    π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) = π.toAlgHom := by
  calc
    π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
        (π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g)).comp
          (HopfAlgebra.pointConjugationAlgHom g⁻¹) := by rw [hg]
    _ = π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom (g⁻¹ * g)) := by
      rw [AlgHom.comp_assoc, HopfAlgebra.pointConjugationAlgHom_mul]
    _ = π.toAlgHom := by
      rw [inv_mul_cancel, HopfAlgebra.pointConjugationAlgHom_one, AlgHom.comp_id]

/-- A rational point of the centralizer normalizes the diagonalizable subgroup. -/
theorem mem_normalizerPoints_of_centralizerHopfIdeal_le_ker (hπ : Function.Surjective π)
    {g : WithConv (H →ₐ[R] R)}
    (hg : (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv) :
    g ∈ normalizerPoints π hπ := by
  rw [mem_normalizerPoints]
  apply HopfIdeal.ext
  intro x
  rw [HopfIdeal.mem_conjugate, HopfIdeal.mem_kerOfSurjective, HopfIdeal.mem_kerOfSurjective]
  have h := AlgHom.congr_fun
    ((centralizerHopfIdeal_le_ker_iff_comp_pointConjugationAlgHom_eq π g).mp hg) x
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom] at h
  rw [h]

/-- **The rational points of the centralizer are the normalizing points acting trivially on the
character group**: the kernel of `BialgHom.normalizerCharacterHom`. -/
theorem normalizerCharacterHom_eq_one_iff_centralizerHopfIdeal_le_ker
    [ConnectedSpace (PrimeSpectrum R)] (hπ : Function.Surjective π)
    (g : normalizerPoints π hπ) :
    normalizerCharacterHom π hπ g = 1 ↔
      (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker (g : WithConv (H →ₐ[R] R)).ofConv := by
  rw [normalizerCharacterHom_eq_one_iff,
    centralizerHopfIdeal_le_ker_iff_comp_pointConjugationAlgHom_eq]
  refine ⟨fun h ↦ ?_, comp_pointConjugationAlgHom_inv_eq_of_comp_eq π⟩
  simpa only [inv_inv] using comp_pointConjugationAlgHom_inv_eq_of_comp_eq π h

/-! ## Comparison with the diagonalizable subgroup -/

/-- **A diagonalizable subgroup lies in its own centralizer**, being commutative. -/
theorem centralizerHopfIdeal_le_kerOfSurjective (hπ : Function.Surjective π) :
    centralizerHopfIdeal π ≤ HopfIdeal.kerOfSurjective π hπ := by
  intro x hx
  have hle : (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker (toConv π.toAlgHom).ofConv := by
    rw [centralizerHopfIdeal_le_ker_iff]
    intro B _ _ φ t
    have hφ : AlgHom.mapValue φ (toConv π.toAlgHom) = BialgHom.mapDomain π (toConv φ) := by
      rw [AlgHom.mapValue_apply, BialgHom.mapDomain_apply, ofConv_toConv, ofConv_toConv]
    rw [hφ]
    exact (Commute.all (toConv φ) t).map (BialgHom.mapDomain π)
  rw [HopfIdeal.mem_kerOfSurjective]
  exact RingHom.mem_ker.mp (hle (HopfIdeal.mem_toIdeal.mpr hx))

/-- A point of `G` killing the kernel of `π` is the image of a point of `D(X)`. -/
private theorem exists_mapDomain_eq_of_forall_mem_kerOfSurjective
    (hπ : Function.Surjective π) {A : Type x} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A))
    (hg : ∀ x : H, x ∈ HopfIdeal.kerOfSurjective π hπ → g.ofConv x = 0) :
    ∃ t : WithConv (MonoidAlgebra R X →ₐ[R] A), BialgHom.mapDomain π t = g := by
  let I := HopfIdeal.kerOfSurjective π hπ
  let g' : H ⧸ I.toIdeal →ₐ[R] A :=
    Ideal.Quotient.liftₐ I.toIdeal g.ofConv fun x hx ↦ hg x (HopfIdeal.mem_toIdeal.mp hx)
  refine ⟨toConv (g'.comp (HopfIdeal.kerLiftBialgEquiv π hπ).symm.toBialgHom.toAlgHom), ?_⟩
  apply ofConv_injective
  ext x
  have he : (HopfIdeal.kerLiftBialgEquiv π hπ).symm (π x) = Ideal.Quotient.mk I.toIdeal x := by
    apply EquivLike.injective (HopfIdeal.kerLiftBialgEquiv π hπ)
    rw [(HopfIdeal.kerLiftBialgEquiv π hπ).apply_symm_apply,
      HopfIdeal.kerLiftBialgEquiv_apply, HopfIdeal.kerLiftBialgHom_mk]
  have hlift := AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I.toIdeal g.ofConv
    fun y hy ↦ hg y (HopfIdeal.mem_toIdeal.mp hy)) x
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hlift
  simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
    BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom, he]
  exact hlift

/-- **The centralizer is the whole group exactly when the diagonalizable subgroup is central.**
-/
theorem centralizerHopfIdeal_eq_bot_iff_isCentral (hπ : Function.Surjective π) :
    centralizerHopfIdeal π = ⊥ ↔ (HopfIdeal.kerOfSurjective π hπ).IsCentral := by
  constructor
  · intro h
    rw [CommHopfAlgCat.isCentral_iff_forall_isCentralPoint (CommHopfAlgCat.of R H)]
    intro A g hg
    obtain ⟨t, rfl⟩ := exists_mapDomain_eq_of_forall_mem_kerOfSurjective π hπ g
      ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hg)
    rw [HopfAlgebra.isCentralPoint_def]
    intro B _ _ φ u
    have hu : (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker u.ofConv := by
      rw [h, HopfIdeal.bot_toIdeal]
      exact bot_le
    have hcomm := commute_mapValue_mapDomain_of_centralizerHopfIdeal_le_ker π hu (AlgHom.id R B)
      (AlgHom.mapValue φ t)
    rw [AlgHom.mapValue_id, MonoidHom.id_apply, ← MonoidHom.comp_apply,
      BialgHom.mapValue_mapDomain, MonoidHom.comp_apply] at hcomm
    exact hcomm.symm
  · intro hI
    let A := CommAlgCat.of R (H ⊗[R] MonoidAlgebra R X)
    have hmem : BialgHom.mapDomain π (toConv ((AlgHom.id R _).comp
        (Algebra.TensorProduct.includeRight : MonoidAlgebra R X →ₐ[R] A))) ∈
        CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of R H)
          (HopfIdeal.kerOfSurjective π hπ) A := by
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro x hx
      rw [HopfIdeal.mem_kerOfSurjective] at hx
      simp [BialgHom.mapDomain_apply, hx]
    have hid : (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker (toConv (AlgHom.id R H)).ofConv :=
      (centralizerHopfIdeal_le_ker_iff_commute_of_injective π (toConv (AlgHom.id R H))
        (AlgHom.id R _) Function.injective_id).mpr
        ((CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup (CommHopfAlgCat.of R H) _
          hI A hmem).commute _).symm
    rw [eq_bot_iff]
    intro x hx
    rw [HopfIdeal.mem_bot]
    exact RingHom.mem_ker.mp (hid (HopfIdeal.mem_toIdeal.mpr hx))

/-! ## Composites `D(Y) → D(X) → G` -/

section Smaller

variable {Y : Type*} [CommGroup Y]

/-- **A smaller diagonalizable subgroup has a larger centralizer.** If `D(Y) → G` factors through
`D(X) → G` along the homomorphism `D(Y) → D(X)` with coordinate map `ψ`, then every point of `G`
centralizing `D(X)` centralizes `D(Y)`. -/
theorem centralizerHopfIdeal_comp_le (ψ : MonoidAlgebra R X →ₐc[R] MonoidAlgebra R Y) :
    centralizerHopfIdeal (ψ.comp π) ≤ centralizerHopfIdeal π := by
  -- Test on the quotient point of `H` by the centralizer ideal of `D(X)`.
  let g : WithConv (H →ₐ[R] H ⧸ (centralizerHopfIdeal π).toIdeal) :=
    toConv (Ideal.Quotient.mkₐ R (centralizerHopfIdeal π).toIdeal)
  have hker : RingHom.ker g.ofConv = (centralizerHopfIdeal π).toIdeal :=
    Ideal.Quotient.mkₐ_ker R _
  have hg : (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv := hker.ge
  have hg' : (centralizerHopfIdeal (ψ.comp π)).toIdeal ≤ RingHom.ker g.ofConv := by
    rw [centralizerHopfIdeal_le_ker_iff]
    intro B _ _ φ t
    rw [BialgHom.mapDomain_comp, MonoidHom.comp_apply]
    exact commute_mapValue_mapDomain_of_centralizerHopfIdeal_le_ker π hg φ _
  rwa [hker, HopfIdeal.toIdeal_le_toIdeal] at hg'

/-- A split injective map of character groups does not change the centralizer of a
composite diagonalizable subgroup. -/
theorem centralizerHopfIdeal_mapDomainBialgHom_comp_eq_of_leftInverse
    (f : X →* Y) (g : Y →* X) (hgf : g.comp f = MonoidHom.id X) :
    centralizerHopfIdeal ((MonoidAlgebra.mapDomainBialgHom R f).comp π) =
      centralizerHopfIdeal π := by
  refine le_antisymm (BialgHom.centralizerHopfIdeal_comp_le _ _) ?_
  have hπ : (MonoidAlgebra.mapDomainBialgHom R g).comp
      ((MonoidAlgebra.mapDomainBialgHom R f).comp π) = π := by
    rw [← BialgHom.comp_assoc, ← MonoidAlgebra.mapDomainBialgHom_comp, hgf,
      MonoidAlgebra.mapDomainBialgHom_id]
    exact BialgHom.id_comp _
  calc
    BialgHom.centralizerHopfIdeal π = BialgHom.centralizerHopfIdeal
        ((MonoidAlgebra.mapDomainBialgHom R g).comp
          ((MonoidAlgebra.mapDomainBialgHom R f).comp π)) :=
      congrArg BialgHom.centralizerHopfIdeal hπ.symm
    _ ≤ _ := BialgHom.centralizerHopfIdeal_comp_le _ _

/-- **The diagonalizable subgroup `D(X)` lies in the centralizer of any composite
`D(Y) → D(X) → G`**, being commutative. -/
theorem centralizerHopfIdeal_comp_le_kerOfSurjective (hπ : Function.Surjective π)
    (ψ : MonoidAlgebra R X →ₐc[R] MonoidAlgebra R Y) :
    centralizerHopfIdeal (ψ.comp π) ≤ HopfIdeal.kerOfSurjective π hπ :=
  (centralizerHopfIdeal_comp_le π ψ).trans (centralizerHopfIdeal_le_kerOfSurjective π hπ)

/-- The centralizer of the diagonalizable subgroup `D(X ⧸ S)` of `D(X)`, the common kernel of the
characters in `S`, grows with `S`. -/
theorem centralizerHopfIdeal_mapDomainBialgHom_mk'_comp_anti {S S' : Subgroup X} (h : S ≤ S') :
    centralizerHopfIdeal ((MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' S')).comp π) ≤
      centralizerHopfIdeal ((MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' S)).comp π) := by
  have hmk : QuotientGroup.mk' S' = (QuotientGroup.map S S' (MonoidHom.id X) h).comp
      (QuotientGroup.mk' S) := by
    ext x
    exact (QuotientGroup.map_mk' S S' (MonoidHom.id X) h x).symm
  rw [hmk, MonoidAlgebra.mapDomainBialgHom_comp, BialgHom.comp_assoc]
  exact centralizerHopfIdeal_comp_le _ _

end Smaller

end BialgHom
