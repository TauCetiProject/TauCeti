/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Character
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Representability
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# The closed normalizer of a diagonalizable subgroup

For a closed diagonalizable subgroup `D(X) → G`, the normalizer is a closed subgroup scheme.
Its equations are the coefficients of universal conjugation applied to the defining ideal
of `D(X)`, together with their antipodes. These two sets of equations require conjugation
by a point and its inverse to preserve the subgroup.

The point criterion tests normalization after every extension of the value algebra. Thus it
captures the subgroup scheme, including its infinitesimal structure, rather than merely its
rational points. The construction works over any commutative ring; smoothness and finite type
are not required. It supplies a represented normalizer for the character action and for
normalizer quotients of split tori.

The coefficient argument follows `TauCeti.Algebra.AlgebraicGroup.Center.Basic`, using the
canonical basis of the group algebra in place of a chosen vector-space basis. The Hopf-ideal
structure comes from `HopfIdeal.ofIdealOfPointsSubgroup`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.j, Proposition 1.83.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

open WithConv TensorProduct

namespace BialgHom

open TauCeti

universe u

noncomputable section

variable {R H X : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)

/-- Points normalizing the diagonalizable subgroup after every extension of their value algebra.
The subgroup at each extension is the image of the points of `D(X)`. -/
def universalNormalizerPoints (A : CommAlgCat.{u} R) : Subgroup (WithConv (H →ₐ[R] A)) :=
  ⨅ (B : CommAlgCat.{u} R) (φ : A →ₐ[R] B),
    (Subgroup.normalizer (AlgHom.mapDomain (A := B) π).range).comap (AlgHom.mapValue φ)

/-- Universal normalization means normalization of the point subgroup over every extension. -/
@[simp]
theorem mem_universalNormalizerPoints (A : CommAlgCat.{u} R) (g : WithConv (H →ₐ[R] A)) :
    g ∈ universalNormalizerPoints π A ↔
      ∀ (B : CommAlgCat.{u} R) (φ : A →ₐ[R] B),
        AlgHom.mapValue φ g ∈ Subgroup.normalizer (AlgHom.mapDomain (A := B) π).range := by
  simp [universalNormalizerPoints]

/-- Changing the value algebra preserves universal normalization. -/
theorem mapValue_mem_universalNormalizerPoints {A B : CommAlgCat.{u} R}
    (φ : A →ₐ[R] B) {g : WithConv (H →ₐ[R] A)}
    (hg : g ∈ universalNormalizerPoints π A) :
    AlgHom.mapValue φ g ∈ universalNormalizerPoints π B := by
  rw [mem_universalNormalizerPoints] at hg ⊢
  intro C ψ
  simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_assoc] using hg C (ψ.comp φ)

/-- The diagonalizable subgroup lies in its universal normalizer. -/
theorem mapDomain_mem_universalNormalizerPoints (A : CommAlgCat.{u} R)
    (t : WithConv (MonoidAlgebra R X →ₐ[R] A)) :
    AlgHom.mapDomain π t ∈ universalNormalizerPoints π A := by
  rw [mem_universalNormalizerPoints]
  intro B φ
  rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_mapDomain, MonoidHom.comp_apply]
  exact Subgroup.le_normalizer ⟨AlgHom.mapValue φ t, rfl⟩

/-- On base-valued points, universal normalization agrees with stabilization of the defining
Hopf ideal, the existing rational normalizer interface. -/
@[simp]
theorem universalNormalizerPoints_base_eq_normalizerPoints :
    universalNormalizerPoints π (CommAlgCat.of R R) = normalizerPoints π hπ := by
  ext g
  constructor
  · intro hg
    let I := HopfIdeal.kerOfSurjective π hπ
    have hle (f : WithConv (H →ₐ[R] R))
        (hf : f ∈ universalNormalizerPoints π (CommAlgCat.of R R)) : I.conjugate f⁻¹ ≤ I := by
      let B := CommAlgCat.of R (MonoidAlgebra R X)
      let t := AlgHom.mapDomain π (toConv (AlgHom.id R (MonoidAlgebra R X)))
      have ht : t ∈ (AlgHom.mapDomain (A := B) π).range := ⟨_, rfl⟩
      have hm := (Subgroup.mem_normalizer_iff.mp
        ((mem_universalNormalizerPoints π (CommAlgCat.of R R) f).mp hf B
          (Algebra.ofId R B)) t).mp ht
      rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range π hπ B,
        ← HopfAlgebra.comp_pointConjugationAlgHom] at hm
      simp only [t, AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.id_comp] at hm
      exact HopfIdeal.conjugate_inv_le_of_mem_quotientPointsSubgroup I I f π.toAlgHom
        (fun x hx ↦ (HopfIdeal.mem_kerOfSurjective π hπ).mpr hx) hm
    rw [mem_normalizerPoints]
    apply le_antisymm
    · simpa only [inv_inv] using hle g⁻¹ (Subgroup.inv_mem _ hg)
    · simpa only [HopfIdeal.conjugate_conjugate_inv] using
        HopfIdeal.conjugate_mono g (hle g hg)
  · intro hg
    rw [mem_normalizerPoints] at hg
    rw [mem_universalNormalizerPoints]
    intro B φ
    have hφ : φ = Algebra.ofId R B := Subsingleton.elim _ _
    rw [hφ, Subgroup.mem_normalizer_iff]
    intro t
    rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range π hπ B]
    simpa only [hg] using (CommHopfAlgCat.pointConjugation_mem_conjugate_iff
      (HopfIdeal.kerOfSurjective π hπ) g B t).symm

/-- A coefficient of the universal conjugation restricted to `D(X)`, in its character basis.
Only coefficients at elements in `ker π` enter the normalizer equations. -/
def normalizerCoefficient (x : H) (i : X) : H := by
  classical
  exact equivFinsuppOfBasisLeft (MonoidAlgebra.basis X R)
    (TensorProduct.comm R H (MonoidAlgebra R X)
      (Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom
        (HopfAlgebra.conjugationAlgHom (R := R) x))) i

attribute [local instance] Classical.decEq

/-- The normalizer coefficient is the indicated coordinate in the character basis. -/
theorem normalizerCoefficient_def (x : H) (i : X) :
    normalizerCoefficient π x i =
      equivFinsuppOfBasisLeft (MonoidAlgebra.basis X R)
        (TensorProduct.comm R H (MonoidAlgebra R X)
          (Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom
            (HopfAlgebra.conjugationAlgHom (R := R) x))) i := by
  classical
  rfl

/-- The equations requiring forward conjugation to preserve the diagonalizable subgroup. -/
private def normalizerCoefficientIdeal : Ideal H :=
  Ideal.span {y | ∃ x : H, π x = 0 ∧ ∃ i : X, normalizerCoefficient π x i = y}

private theorem normalizerCoefficientIdeal_le_ker_iff
    {A : Type u} [CommRing A] [Algebra R A] (g : H →ₐ[R] A) :
    normalizerCoefficientIdeal π ≤ RingHom.ker g ↔
      ∀ x : H, π x = 0 →
        Algebra.TensorProduct.map g π.toAlgHom
          (HopfAlgebra.conjugationAlgHom (R := R) x) = 0 := by
  classical
  rw [normalizerCoefficientIdeal, Ideal.span_le]
  have hcoeff (x : H) :
      Algebra.TensorProduct.map g π.toAlgHom
          (HopfAlgebra.conjugationAlgHom (R := R) x) = 0 ↔
        ∀ i, g (normalizerCoefficient π x i) = 0 := by
    rw [← (TensorProduct.comm R A (MonoidAlgebra R X)).map_eq_zero_iff]
    have hmap :
        TensorProduct.comm R A (MonoidAlgebra R X)
            (Algebra.TensorProduct.map g π.toAlgHom
              (HopfAlgebra.conjugationAlgHom (R := R) x)) =
          g.toLinearMap.lTensor (MonoidAlgebra R X)
            (TensorProduct.comm R H (MonoidAlgebra R X)
              (Algebra.TensorProduct.map (AlgHom.id R H) π.toAlgHom
                (HopfAlgebra.conjugationAlgHom (R := R) x))) := by
      simp only [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
        TensorProduct.AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id,
        LinearMap.lTensor_def, TensorProduct.map_comm, TensorProduct.map_map,
        LinearMap.comp_id, LinearMap.id_comp]
    rw [hmap, (MonoidAlgebra.basis X R).lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft]
    rfl
  constructor
  · intro h x hx
    exact (hcoeff x).mpr fun i ↦ RingHom.mem_ker.mp (h ⟨x, hx, i, rfl⟩)
  · rintro h y ⟨x, hx, i, rfl⟩
    exact RingHom.mem_ker.mpr ((hcoeff x).mp (h x hx) i)

private theorem map_conjugation_eq_universal_conjugate
    {A : Type u} [CommRing A] [Algebra R A] (g : WithConv (H →ₐ[R] A)) :
    toConv ((Algebra.TensorProduct.map g.ofConv π.toAlgHom).comp
        (HopfAlgebra.conjugationAlgHom (R := R) (H := H))) =
      AlgHom.mapValue (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] MonoidAlgebra R X) g *
        AlgHom.mapDomain π
          (toConv (Algebra.TensorProduct.includeRight :
            MonoidAlgebra R X →ₐ[R] A ⊗[R] MonoidAlgebra R X)) *
        (AlgHom.mapValue Algebra.TensorProduct.includeLeft g)⁻¹ := by
  rw [HopfAlgebra.comp_conjugationAlgHom, toConv_ofConv]
  simp only [Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight, AlgHom.mapValue_apply, AlgHom.mapDomain_apply]

include hπ in
private theorem conjugation_vanishes_iff
    (A : CommAlgCat.{u} R) (g : WithConv (H →ₐ[R] A)) :
    (∀ x : H, π x = 0 →
      Algebra.TensorProduct.map g.ofConv π.toAlgHom
        (HopfAlgebra.conjugationAlgHom (R := R) x) = 0) ↔
      ∀ (B : CommAlgCat.{u} R) (φ : A →ₐ[R] B)
        (t : WithConv (MonoidAlgebra R X →ₐ[R] B)),
        AlgHom.mapValue φ g * AlgHom.mapDomain π t * (AlgHom.mapValue φ g)⁻¹ ∈
          (AlgHom.mapDomain (A := B) π).range := by
  constructor
  · intro h B φ t
    rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range π hπ B,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    have heval :
        (Algebra.TensorProduct.productMap φ t.ofConv).comp
            (Algebra.TensorProduct.map g.ofConv π.toAlgHom) =
          Algebra.TensorProduct.productMap (φ.comp g.ofConv) (t.ofConv.comp π.toAlgHom) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp
    have hz := congrArg (Algebra.TensorProduct.productMap φ t.ofConv)
      (h x ((HopfIdeal.mem_kerOfSurjective π hπ).mp hx))
    have hc := AlgHom.congr_fun
      (HopfAlgebra.productMap_comp_conjugationAlgHom
        (AlgHom.mapValue φ g) (AlgHom.mapDomain π t)) x
    rw [← AlgHom.comp_apply, heval, map_zero] at hz
    have hz' : ((Algebra.TensorProduct.productMap (AlgHom.mapValue φ g).ofConv
        (AlgHom.mapDomain π t).ofConv).comp
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H))) x = 0 := by
      simpa only [AlgHom.mapValue_apply, AlgHom.mapDomain_apply, ofConv_toConv,
        AlgHom.comp_apply] using hz
    exact hc.symm.trans hz'
  · intro h x hx
    let B := CommAlgCat.of R (A ⊗[R] MonoidAlgebra R X)
    have hm := h B Algebra.TensorProduct.includeLeft (toConv Algebra.TensorProduct.includeRight)
    rw [← map_conjugation_eq_universal_conjugate π] at hm
    rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range π hπ B,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hm
    exact hm x ((HopfIdeal.mem_kerOfSurjective π hπ).mpr hx)

include hπ in
private theorem normalizer_equations_iff
    (A : CommAlgCat.{u} R) (g : WithConv (H →ₐ[R] A)) :
    (normalizerCoefficientIdeal π ≤ RingHom.ker g.ofConv ∧
      normalizerCoefficientIdeal π ≤ RingHom.ker g⁻¹.ofConv) ↔
        g ∈ universalNormalizerPoints π A := by
  rw [normalizerCoefficientIdeal_le_ker_iff, normalizerCoefficientIdeal_le_ker_iff,
    conjugation_vanishes_iff π hπ, conjugation_vanishes_iff π hπ,
    mem_universalNormalizerPoints]
  constructor
  · rintro ⟨hg, hi⟩ B φ
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · rintro ⟨s, rfl⟩
      exact hg B φ s
    · intro ht
      obtain ⟨s, hs⟩ := ht
      have hinv := hi B φ s
      rw [map_inv, hs] at hinv
      simpa [mul_assoc] using hinv
  · intro hg
    constructor
    · intro B φ t
      exact (Subgroup.mem_normalizer_iff.mp (hg B φ) _).mp ⟨t, rfl⟩
    · intro B φ t
      rw [map_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (hg B φ)) _).mp ⟨t, rfl⟩

/-- The equations requiring both forward and inverse conjugation to preserve the subgroup. -/
private def normalizerIdeal : Ideal H :=
  normalizerCoefficientIdeal π ⊔
    Ideal.map (_root_.HopfAlgebra.antipodeAlgHom R H) (normalizerCoefficientIdeal π)

include hπ in
private theorem normalizerIdeal_le_ker_iff
    (A : CommAlgCat.{u} R) (g : WithConv (H →ₐ[R] A)) :
    normalizerIdeal π ≤ RingHom.ker g.ofConv ↔ g ∈ universalNormalizerPoints π A := by
  rw [normalizerIdeal, sup_le_iff, Ideal.map_le_iff_le_comap]
  have hker : Ideal.comap (_root_.HopfAlgebra.antipodeAlgHom R H)
      (RingHom.ker g.ofConv) = RingHom.ker g⁻¹.ofConv := by
    ext x
    simp only [Ideal.mem_comap, RingHom.mem_ker,
      _root_.HopfAlgebra.antipodeAlgHom_apply, AlgHom.convInv_apply]
  rw [hker]
  exact normalizer_equations_iff π hπ A g

/-- The Hopf ideal cutting out the closed normalizer of `D(X) → G`.
Its quotient represents normalization of the subgroup after every value-algebra extension. -/
def normalizerHopfIdeal : HopfIdeal R H :=
  HopfIdeal.ofIdealOfPointsSubgroup (normalizerIdeal π)
    (universalNormalizerPoints π) (fun A g ↦ (normalizerIdeal_le_ker_iff π hπ A g).symm)

/-- The normalizer ideal is generated by the conjugation coefficients and their antipodes. -/
@[simp]
theorem normalizerHopfIdeal_toIdeal :
    (normalizerHopfIdeal π hπ).toIdeal =
      Ideal.span {y | ∃ x : H, π x = 0 ∧ ∃ i : X, normalizerCoefficient π x i = y} ⊔
        Ideal.map (_root_.HopfAlgebra.antipodeAlgHom R H)
          (Ideal.span {y | ∃ x : H, π x = 0 ∧ ∃ i : X, normalizerCoefficient π x i = y}) := by
  rw [normalizerHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]
  rfl

/-- A point annihilates the normalizer ideal exactly when it normalizes the subgroup universally. -/
theorem normalizerHopfIdeal_le_ker_iff
    (A : CommAlgCat.{u} R) (g : WithConv (H →ₐ[R] A)) :
    (normalizerHopfIdeal π hπ).toIdeal ≤ RingHom.ker g.ofConv ↔
      g ∈ universalNormalizerPoints π A := by
  rw [normalizerHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]
  exact normalizerIdeal_le_ker_iff π hπ A g

/-- The closed subgroup represented by the normalizer ideal has exactly the universal normalizer
points over every commutative value algebra. -/
@[simp]
theorem quotientPointsSubgroup_normalizerHopfIdeal (A : CommAlgCat.{u} R) :
    CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H)
        (normalizerHopfIdeal π hπ) A = universalNormalizerPoints π A := by
  ext g
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, ← normalizerHopfIdeal_le_ker_iff π hπ]
  exact forall_congr' fun x ↦ by
    simp only [← HopfIdeal.mem_toIdeal, RingHom.mem_ker]

/-- The normalizer contains the original closed diagonalizable subgroup. The order on defining
ideals reverses the inclusion of closed subgroup schemes. -/
theorem normalizerHopfIdeal_le_kerOfSurjective :
    normalizerHopfIdeal π hπ ≤ HopfIdeal.kerOfSurjective π hπ := by
  have hg := mapDomain_mem_universalNormalizerPoints π
    (CommAlgCat.of R (MonoidAlgebra R X)) (toConv (AlgHom.id R (MonoidAlgebra R X)))
  have hker := (normalizerHopfIdeal_le_ker_iff π hπ _ _).mpr hg
  intro x hx
  apply (HopfIdeal.mem_kerOfSurjective π hπ).mpr
  simpa only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    AlgHom.id_apply, BialgHom.coe_toAlgHom]
    using RingHom.mem_ker.mp (hker (HopfIdeal.mem_toIdeal.mpr hx))

end

end BialgHom
