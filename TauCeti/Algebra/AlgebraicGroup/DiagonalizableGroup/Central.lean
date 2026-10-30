/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import TauCeti.Algebra.AlgebraicGroup.Derived.Character
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Central diagonalizable subgroups and the derived subgroup

Let `D(X) → G` be a closed diagonalizable subgroup of an affine group `G = Spec H`, given by a
surjective coordinate map `π : H → R[X]`. When `D(X)` is central, `G` preserves the weight
decomposition of every representation under `D(X)`: each weight space is a subrepresentation.

Over a field, this gives the standard determinant argument for the intersection of `D(X)` with
the derived subgroup `[G, G]`. The determinant of the `x`-weight space of a representation is a
character of `G`, so it is trivial on `[G, G]`, while on `D(X)` it is `x ^ d`, where `d` is the
dimension of that weight space. Hence every weight occurring in a coefficient-generating
representation has finite order on `D(X) ∩ [G, G]`. These weights generate the coordinate
algebra of the intersection, which is therefore finite-dimensional. Applied over an
algebraically closed field to the central torus `Z(G)°` of a reductive group, this is the
finiteness of `Z(G)° ∩ [G, G]`.

The hypothesis of the weight-space statement is that `π` restricts the comultiplication
symmetrically, which is the coordinate form of centrality: it follows from triviality of the
centralizer ideal `BialgHom.centralizerHopfIdeal π`.

## Main declarations

* `BialgHom.map_comul_eq_comm_map_comul_of_centralizerHopfIdeal_eq_bot`: a central
  diagonalizable subgroup restricts the comultiplication symmetrically.
* `TauCeti.DiagonalizableGroup.weightSubcomodule`: the weight spaces of a central diagonalizable
  subgroup are subcomodules.
* `BialgHom.exists_groupLike_map_eq_single_pow_of_weightSpace_ne_bot`: a positive power of each
  occurring weight of a central diagonalizable subgroup extends to a character of the ambient
  group.
* `BialgHom.moduleFinite_quotient_sup_derivedDefiningIdeal`: **a central diagonalizable subgroup
  of an affine group of finite type over a field meets the derived subgroup in a finite
  subgroup.**

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §14.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 19.
-/

public section

open scoped TensorProduct

open TauCeti WithConv

namespace BialgHom

variable {R H X : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]

/-- **A central diagonalizable subgroup restricts the comultiplication symmetrically.** If the
centralizer of `D(X) → G` is all of `G`, then restricting the comultiplication of `H` to `D(X)`
in the right factor agrees with restricting it in the left factor, up to exchanging the two
factors. This is the coordinate form of `g t = t g` for the universal points `g` of `G` and `t`
of `D(X)`. -/
theorem map_comul_eq_comm_map_comul_of_centralizerHopfIdeal_eq_bot
    (π : H →ₐc[R] MonoidAlgebra R X) (hπ : centralizerHopfIdeal π = ⊥) (h : H) :
    TensorProduct.map LinearMap.id π.toLinearMap (Coalgebra.comul h) =
      TensorProduct.comm R (MonoidAlgebra R X) H
        (TensorProduct.map π.toLinearMap LinearMap.id (Coalgebra.comul h)) := by
  have hcomm := (centralizerHopfIdeal_le_ker_iff_commute_of_injective π
    (toConv (AlgHom.id R H)) (AlgHom.id R (H ⊗[R] MonoidAlgebra R X))
    Function.injective_id).mp (by simp [hπ])
  have heq := congrArg (fun f ↦ f.ofConv h) hcomm.eq
  simp only [AlgHom.convMul_apply] at heq
  convert heq using 1 <;> generalize Coalgebra.comul (R := R) h = t <;>
    induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    simp [AlgHom.mapValue_apply, BialgHom.mapDomain_apply, BialgHom.toCoalgHom_apply]

end BialgHom

namespace TauCeti.DiagonalizableGroup

variable {R C X : Type*} [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]
variable (V : Type*) [AddCommGroup V] [Module R V] [Comodule R C V]

/-- If `π` restricts the comultiplication symmetrically, the coaction of an `x`-weight vector
satisfies the `x`-weight equation in its first tensor factor. -/
private theorem rTensor_comp_coact_of_mem_weightSpace (π : C →ₗc[R] MonoidAlgebra R X)
    (hπ : ∀ c : C, TensorProduct.map LinearMap.id π.toLinearMap (Coalgebra.comul c) =
      TensorProduct.comm R (MonoidAlgebra R X) C
        (TensorProduct.map π.toLinearMap LinearMap.id (Coalgebra.comul c)))
    {x : X} {v : V} (hv : v ∈ weightSpace V π x) :
    (TensorProduct.map LinearMap.id π.toLinearMap ∘ₗ
        Comodule.coact (R := R) (C := C) (M := V)).rTensor C
        (Comodule.coact (R := R) (C := C) (M := V) v) =
      ((TensorProduct.mk R V (MonoidAlgebra R X)).flip (MonoidAlgebra.single x 1)).rTensor C
        (Comodule.coact (R := R) (C := C) (M := V) v) := by
  rw [mem_weightSpace] at hv
  set ρ := Comodule.coact (R := R) (C := C) (M := V)
  set P := π.toLinearMap
  set s : MonoidAlgebra R X := MonoidAlgebra.single x 1
  have hcomul (c : C) : TensorProduct.map P LinearMap.id (Coalgebra.comul c) =
      TensorProduct.comm R C (MonoidAlgebra R X)
        (TensorProduct.map LinearMap.id P (Coalgebra.comul c)) := by
    rw [hπ c, TensorProduct.comm_comm]
  -- Coassociativity turns the left-hand side into `ρ v ⊗ s` with its last two factors swapped.
  have hcoassoc : ρ.rTensor C (ρ v) =
      (TensorProduct.assoc R V C C).symm (Coalgebra.comul.lTensor V (ρ v)) := by
    rw [← Comodule.coassoc_apply, LinearEquiv.symm_apply_apply]
  have hassoc : (TensorProduct.map LinearMap.id P).lTensor V (Coalgebra.comul.lTensor V (ρ v)) =
      TensorProduct.assoc R V C (MonoidAlgebra R X) (ρ v ⊗ₜ s) := by
    rw [← Comodule.coassoc_apply, ← LinearMap.rTensor_tmul (M := MonoidAlgebra R X) ρ, ← hv]
    generalize ρ v = t
    induction t using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul w c =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
      induction ρ w using TensorProduct.inductionOn with
      | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz]
      | tmul u d => simp
  have hswap : TensorProduct.map LinearMap.id (TensorProduct.map P LinearMap.id)
      (Coalgebra.comul.lTensor V (ρ v)) =
      (TensorProduct.comm R C (MonoidAlgebra R X)).toLinearMap.lTensor V
        ((TensorProduct.map LinearMap.id P).lTensor V (Coalgebra.comul.lTensor V (ρ v))) := by
    generalize ρ v = t
    induction t using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul w c => simp [hcomul]
  have hsymm (t : V ⊗[R] (C ⊗[R] C)) :
      (TensorProduct.map LinearMap.id P).rTensor C ((TensorProduct.assoc R V C C).symm t) =
        (TensorProduct.assoc R V (MonoidAlgebra R X) C).symm
          (TensorProduct.map LinearMap.id (TensorProduct.map P LinearMap.id) t) := by
    rw [LinearMap.rTensor_def]
    exact TensorProduct.map_map_assoc_symm _ _ _ t
  rw [LinearMap.rTensor_comp_apply, hcoassoc, hsymm, hswap, hassoc]
  generalize ρ v = t
  induction t using TensorProduct.inductionOn with
  | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz]
  | tmul w c => simp [s]

variable [Module.Flat R C]

/-- **The weight spaces of a central diagonalizable subgroup are subrepresentations.** If a
coalgebra morphism `π : C → R[X]` restricts the comultiplication of a flat coalgebra `C`
symmetrically, then each weight space of a right `C`-comodule `V` is a subcomodule. For a closed
diagonalizable subgroup `D(X)` of an affine group `G`, the hypothesis says that `D(X)` is
central (`BialgHom.map_comul_eq_comm_map_comul_of_centralizerHopfIdeal_eq_bot`), and the
conclusion that `G` preserves the decomposition of every representation into `D(X)`-weight
spaces. -/
noncomputable def weightSubcomodule (π : C →ₗc[R] MonoidAlgebra R X)
    (hπ : ∀ c : C, TensorProduct.map LinearMap.id π.toLinearMap (Coalgebra.comul c) =
      TensorProduct.comm R (MonoidAlgebra R X) C
        (TensorProduct.map π.toLinearMap LinearMap.id (Coalgebra.comul c)))
    (x : X) : Subcomodule R C V :=
  Subcomodule.ofSubmodule (weightSpace V π x) fun v hv ↦ by
    let f : V →ₗ[R] V ⊗[R] MonoidAlgebra R X :=
      TensorProduct.map LinearMap.id π.toLinearMap ∘ₗ Comodule.coact (R := R) (C := C) (M := V) -
        (TensorProduct.mk R V (MonoidAlgebra R X)).flip (MonoidAlgebra.single x 1)
    have hker : weightSpace V π x = LinearMap.ker f := by
      ext w
      simp [f, mem_weightSpace, sub_eq_zero]
    rw [hker]
    exact (Module.Flat.rTensor_exact C (LinearMap.exact_subtype_ker_map f) _).mp (by
      rw [LinearMap.rTensor_sub, LinearMap.sub_apply,
        rTensor_comp_coact_of_mem_weightSpace V π hπ hv, sub_self])

variable {V} {π : C →ₗc[R] MonoidAlgebra R X}
  {hπ : ∀ c : C, TensorProduct.map LinearMap.id π.toLinearMap (Coalgebra.comul c) =
    TensorProduct.comm R (MonoidAlgebra R X) C
      (TensorProduct.map π.toLinearMap LinearMap.id (Coalgebra.comul c))}

/-- The underlying submodule of a weight subcomodule is the weight space. -/
@[simp]
theorem weightSubcomodule_toSubmodule (x : X) :
    (weightSubcomodule V π hπ x).toSubmodule = weightSpace V π x :=
  (rfl)

/-- Membership in a weight subcomodule is membership in the corresponding weight space. -/
@[simp]
theorem mem_weightSubcomodule {x : X} {v : V} :
    v ∈ weightSubcomodule V π hπ x ↔ v ∈ weightSpace V π x :=
  (Iff.rfl)

/-- With its inherited coaction, the `x`-weight subcomodule has pure weight `x`. -/
theorem mem_weightSpace_weightSubcomodule (x : X) (n : weightSubcomodule V π hπ x) :
    n ∈ weightSpace (weightSubcomodule V π hπ x) π x := by
  rw [mem_weightSpace]
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := MonoidAlgebra R X)
    (SMulMemClass.subtype (weightSubcomodule V π hπ x)) Subtype.val_injective
  rw [LinearMap.rTensor_tmul, SMulMemClass.subtype_apply, ← mem_weightSpace.mp n.2,
    ← Subcomodule.subtype_rTensor_coact _ n]
  generalize Comodule.coact (R := R) (C := C) n = t
  induction t using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul y c => simp

end TauCeti.DiagonalizableGroup

namespace BialgHom

open TauCeti.DiagonalizableGroup

variable {k H X : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]

/-- **A weight of a central diagonalizable subgroup has a power extending to a character.** If
`D(X)` is central in `G` and `x` occurs as a weight of a finite-dimensional representation `V`,
then some positive power `x ^ n` is the restriction to `D(X)` of a character of `G`. -/
theorem exists_groupLike_map_eq_single_pow_of_weightSpace_ne_bot
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : centralizerHopfIdeal π = ⊥)
    {V : Type*} [AddCommMonoid V] [Module k V] [Comodule k H V] [Module.Finite k V] {x : X}
    (hx : weightSpace V π.toCoalgHom x ≠ ⊥) :
    ∃ n, 0 < n ∧ ∃ g : GroupLike k H, π g = MonoidAlgebra.single (x ^ n) 1 := by
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let N := weightSubcomodule V π.toCoalgHom
    (map_comul_eq_comm_map_comul_of_centralizerHopfIdeal_eq_bot π hπ) x
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  have : Module.Finite k N :=
    Module.Finite.of_injective (SMulMemClass.subtype N) Subtype.val_injective
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hx
  let b := Module.finBasis k N
  refine ⟨Module.finrank k N, Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨(⟨v, hv⟩ : N), fun h ↦ hv0 (congrArg Subtype.val h)⟩,
    ⟨(Comodule.coefficientMatrix (C := H) b).det,
      Comodule.isGroupLikeElem_det_coefficientMatrix b⟩, ?_⟩
  simpa using map_det_coefficientMatrix_of_forall_mem_weightSpace π
    (mem_weightSpace_weightSubcomodule x) b

/-- **A central diagonalizable subgroup meets the derived subgroup in a finite subgroup**, given
a finite-dimensional representation whose matrix coefficients generate the coordinate algebra.
Assuming such a representation in place of `Algebra.FiniteType k H`, the coordinate algebra of
`D(X) ∩ [G, G]` is finite-dimensional. -/
theorem moduleFinite_quotient_sup_derivedDefiningIdeal_of_matrixCoefficientSubalgebra_eq_top
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hcentral : (HopfIdeal.kerOfSurjective π hπ).IsCentral)
    {V : Type*} [AddCommMonoid V] [Module k V] [Comodule k H V] [Module.Finite k V]
    (hV : Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := V) = ⊤) :
    Module.Finite k
      (H ⧸ (HopfIdeal.kerOfSurjective π hπ ⊔
        CommHopfAlgCat.derivedDefiningIdeal (R := k) H).toIdeal) := by
  set L := HopfIdeal.kerOfSurjective π hπ ⊔ CommHopfAlgCat.derivedDefiningIdeal (R := k) H
  set q := Ideal.Quotient.mkₐ k L.toIdeal
  -- Restriction to `D(X) ∩ [G, G]` factors through restriction to `D(X)`.
  have hker : RingHom.ker π.toAlgHom.toRingHom ≤ RingHom.ker q.toRingHom := fun h hh ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (by
      rw [HopfIdeal.sup_toIdeal]
      exact Ideal.mem_sup_left (by rwa [HopfIdeal.kerOfSurjective_toIdeal]))
  let ψ := AlgHom.liftOfSurjective π.toAlgHom hπ q hker
  have hψ (h : H) : ψ (π h) = q h := AlgHom.liftOfSurjective_apply π.toAlgHom hπ q hker h
  set W := {x : X | weightSpace V π.toCoalgHom x ≠ ⊥}
  set S := (fun x ↦ ψ (MonoidAlgebra.single x 1)) '' W
  -- Each occurring weight has finite order on `D(X) ∩ [G, G]`.
  have hint : ∀ s ∈ S, IsIntegral k s := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, g, hg⟩ := exists_groupLike_map_eq_single_pow_of_weightSpace_ne_bot π
      ((centralizerHopfIdeal_eq_bot_iff_isCentral π hπ).mpr hcentral) hx
    have hpow : ψ (MonoidAlgebra.single x 1) ^ n = 1 := by
      rw [← map_pow, MonoidAlgebra.single_pow, one_pow, ← hg, hψ, ← map_one q]
      exact Ideal.Quotient.eq.mpr (by
        rw [HopfIdeal.sup_toIdeal]
        exact Ideal.mem_sup_right (GroupLike.sub_one_mem_derivedDefiningIdeal g))
    exact IsIntegral.of_pow hn (hpow ▸ isIntegral_one)
  -- The matrix coefficients generate `H`, and they restrict into the span of the weights.
  have htop : Algebra.adjoin k S = ⊤ := by
    have hle : Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := V) ≤
        (Algebra.adjoin k S).comap q := by
      refine Comodule.matrixCoefficientSubalgebra_le_iff.mpr fun φ v ↦ ?_
      have hspan := map_matrixCoefficient_mem_span_single π.toCoalgHom φ v
      rw [BialgHom.toCoalgHom_apply] at hspan
      rw [Subalgebra.mem_comap, ← hψ]
      have hmap := Submodule.mem_map_of_mem (f := ψ.toLinearMap) hspan
      rw [Submodule.map_span, ← Set.image_comp] at hmap
      exact (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin k S))).mpr
        (fun _ hs ↦ Algebra.subset_adjoin hs) hmap
    rw [hV] at hle
    rw [eq_top_iff]
    rintro y -
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective k L.toIdeal y
    exact hle Algebra.mem_top
  rw [Module.finite_def, ← Algebra.top_toSubmodule, ← htop]
  exact fg_adjoin_of_finite ((finite_setOf_weightSpace_ne_bot V π.toCoalgHom).image _) hint

/-- **A central diagonalizable subgroup of an affine group of finite type over a field meets
the derived subgroup in a finite subgroup.** In coordinates: if `π : H → k[X]` cuts out a central
closed diagonalizable subgroup `D(X)` of `G = Spec H`, then the coordinate algebra of
`D(X) ∩ [G, G]` is finite-dimensional. -/
theorem moduleFinite_quotient_sup_derivedDefiningIdeal [Algebra.FiniteType k H]
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hcentral : (HopfIdeal.kerOfSurjective π hπ).IsCentral) :
    Module.Finite k
      (H ⧸ (HopfIdeal.kerOfSurjective π hπ ⊔
        CommHopfAlgCat.derivedDefiningIdeal (R := k) H).toIdeal) := by
  obtain ⟨V, hfinite, hV⟩ :=
    Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top (k := k) (C := H)
  let : Module.Finite k V := hfinite
  exact moduleFinite_quotient_sup_derivedDefiningIdeal_of_matrixCoefficientSubalgebra_eq_top
    π hπ hcentral hV

end BialgHom
