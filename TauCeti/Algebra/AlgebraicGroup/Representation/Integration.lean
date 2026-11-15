/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
import TauCeti.Algebra.AlgebraicGroup.Representation.Kernel
import TauCeti.Algebra.AlgebraicGroup.Tangent.Rigidity

/-!
# Infinitesimal uniqueness of comodules and Tannakian descent of group homomorphisms

This file provides general representation-theoretic tools for integrating Lie-algebra actions and
Lie-algebra homomorphisms on connected affine algebraic groups:

1. **Differentials of direct sums and linear transports.** Over any commutative ring `R` and
   commutative bialgebra `H`, the differentiated action `Comodule.differential` acts componentwise
   on `M × N` (`TauCeti.Comodule.differential_prod`) and conjugates across a linear equivalence
   `e : M ≃ₗ[R] N` (`TauCeti.Comodule.differential_transport`).
2. **Infinitesimal uniqueness of rational representations.** Over an algebraically closed field `k`
   of characteristic zero, if `Spec H` is connected and of finite type, two `H`-comodule structures
   on the same `k`-vector space with equal differentiated actions coincide
   (`TauCeti.Comodule.ext_of_differential_eq`), without any finite-dimensionality hypothesis on the
   representation.
3. **Tannakian descent of group homomorphisms along a faithful representation.** Given a connected
   finite-type group `Spec K` and an affine group `Spec H` equipped with a finite-free comodule `M`
   whose coordinate morphism `O(GLₙ) → H` is surjective, any Lie homomorphism `ψ : Lie(K) → Lie(H)`
   whose restricted `Lie(K)`-action on `M` integrates to a `K`-comodule descends uniquely to a
   bialgebra morphism `H →ₐc[k] K` with differential `ψ`
   (`TauCeti.CommHopfAlgCat.existsUnique_bialgHom_derivationCompLieHom_eq_of_surjective`).

## Main declarations

* `TauCeti.Comodule.differential_prod`: differential of `Comodule.Prod`.
* `TauCeti.Comodule.differential_transport`: differential of `Comodule.Transport`.
* `TauCeti.Comodule.ext_of_differential_eq`: uniqueness of comodules with equal differentials over a
  connected finite-type group in characteristic zero.
* `TauCeti.CommHopfAlgCat.existsUnique_bialgHom_derivationCompLieHom_eq_of_surjective`: unique
  descent of `ψ : Lie(K) → Lie(H)` to `H →ₐc[k] K` from an integrating `K`-comodule on a faithful
  `H`-comodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open CategoryTheory Module

namespace TauCeti

universe u v w

namespace Comodule

section CommRing

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [Bialgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The differentiated action on a direct-sum comodule `M × N` acts componentwise. -/
theorem differential_prod {N : Type*} [AddCommGroup N] [Module R N] [Comodule R H N]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (x : M × N) :
    letI : Comodule R H (M × N) := Comodule.Prod
    differential (R := R) (H := H) (M := M × N) d x =
      (differential (R := R) (H := H) (M := M) d x.1,
        differential (R := R) (H := H) (M := N) d x.2) := by
  let _ : Comodule R H (M × N) := Comodule.Prod
  apply Prod.ext
  · simpa only [prodFst_apply] using
      (prodFst (R := R) (C := H) (M := M) (N := N)).map_differential d x
  · simpa only [prodSnd_apply] using
      (prodSnd (R := R) (C := H) (M := M) (N := N)).map_differential d x

/-- Transporting a comodule across a linear equivalence `e : M ≃ₗ[R] N` conjugates the
differentiated representation by `e`. -/
theorem differential_transport {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (n : N) :
    letI : Comodule R H N := Transport (R := R) (C := H) e
    differential (R := R) (H := H) (M := N) d n =
      e (differential (R := R) (H := H) (M := M) d (e.symm n)) := by
  let _ : Comodule R H N := Transport (R := R) (C := H) e
  let f : Hom R H M N :=
    { toLinearMap := e.toLinearMap
      map_coact := by
        ext m
        simp }
  simpa only [f, Hom.coe_mk, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
    (f.map_differential d (e.symm n)).symm

end CommRing

section Unique

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
variable {M : Type w} [AddCommGroup M] [Module k M]

/-- Over an algebraically closed field of characteristic zero, a comodule structure over a
connected finite-type affine group is uniquely determined by its differentiated representation.
No finite-dimensionality assumption on `M` is needed. -/
theorem ext_of_differential_eq (c₁ c₂ : Comodule k H M)
    (h : ∀ (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M),
      @differential k H M _ _ _ _ _ c₁ d m = @differential k H M _ _ _ _ _ c₂ d m) :
    c₁ = c₂ := by
  have hcoact :=
    (@LinearMap.map_coact_iff_map_differential k _ _ _ H _ M _ _ c₁ M _ _ c₂ LinearMap.id).mpr h
  ext m
  simpa using LinearMap.congr_fun hcoact m

end Unique

end Comodule

namespace CommHopfAlgCat

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

/-- Let `K` represent a connected finite-type affine group over an algebraically closed field of
characteristic zero, and let `b` be a finite basis of an `H`-comodule `M` whose coordinate
morphism `O(GLₙ) → H` is surjective. Any Lie homomorphism `ψ : Lie(K) → Lie(H)` for which the
restricted `Lie(K)`-action on `M` integrates to a `K`-comodule lifts to a unique bialgebra morphism
`H →ₐc[k] K` with differential `ψ`. -/
theorem existsUnique_bialgHom_derivationCompLieHom_eq_of_surjective
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    {K : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum K)]
    (ψ : Derivation k K (Bialgebra.CounitAlgebra k K k) →ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k))
    {M : Type w} [AddCommGroup M] [Module k M] [cH : Comodule k H M]
    {n : ℕ} (b : Basis (Fin n) k M)
    (hb : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (cK : Comodule k K M)
    (hcK : ∀ (d : Derivation k K (Bialgebra.CounitAlgebra k K k)) (m : M),
      @Comodule.differential k K M _ _ _ _ _ cK d m =
        @Comodule.differential k H M _ _ _ _ _ cH (ψ d) m) :
    ∃! f : H →ₐc[k] K, derivationCompLieHom (B := k) f = ψ := by
  let π : GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] H :=
    Comodule.coordinateBialgHom (H := H) b
  let ρ : GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] K :=
    @Comodule.coordinateBialgHom k K M _ _ _ _ _ cK n b
  have hdiff (d : Derivation k K (Bialgebra.CounitAlgebra k K k)) :
      derivationComp ρ d = derivationComp π (ψ d) := by
    apply (GeneralLinear.tangentLinearEquivMatrix (R := k) (B := k) n).injective
    rw [GeneralLinear.tangentLinearEquivMatrix_apply, GeneralLinear.tangentLinearEquivMatrix_apply,
      @Derivation.tangentMatrix_comp_coordinateBialgHom k K M _ _ _ _ _ cK n d b,
      Derivation.tangentMatrix_comp_coordinateBialgHom (ψ d) b]
    congr 1
    ext m
    exact hcK d m
  let I := HopfIdeal.kerOfSurjective π hb
  let J : HopfIdeal k K := I.map ρ
  let _ : Algebra.Smooth k K :=
    (smoothCommHopfAlgProperty_iff K.obj).mp (smoothCommHopfAlgProperty_of_charZero k K.obj)
  let _ : Algebra.Smooth k (K ⧸ J.toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_charZero k (_root_.CommHopfAlgCat.of k (K ⧸ J.toIdeal)))
  have hJtop : J.lieSubalgebra (B := k) = ⊤ := by
    rw [eq_top_iff]
    intro d _
    rw [HopfIdeal.lieSubalgebra_map, LieSubalgebra.mem_comap, derivationCompLieHom_apply,
      hdiff d, HopfIdeal.mem_lieSubalgebra_iff]
    intro x hx
    have hx0 : π x = 0 := (HopfIdeal.mem_kerOfSurjective π hb).mp hx
    apply (Bialgebra.CounitAlgebra.algEquivSelf k _ k).injective
    rw [algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom, hx0, Derivation.map_zero,
      map_zero, map_zero]
  have hJbot : J = ⊥ := HopfIdeal.eq_bot_of_lieSubalgebra_eq_top J hJtop
  have hle : I.toIdeal ≤ RingHom.ker ρ.toAlgHom.toRingHom := by
    intro x hx
    have hxJ : ρ x ∈ J := HopfIdeal.mem_map_of_mem ρ hx
    rw [hJbot, HopfIdeal.mem_bot] at hxJ
    exact hxJ
  let eπ := HopfIdeal.kerLiftBialgEquiv π hb
  let f : H →ₐc[k] K :=
    (Bialgebra.Quotient.liftBialgHom I.toIdeal ρ hle).comp (eπ.symm : H →ₐc[k] _)
  have hfπ : f.comp π = ρ := by
    ext x
    have hsymm : eπ.symm (π x) = Ideal.Quotient.mk I.toIdeal x :=
      eπ.symm_apply_eq.mpr
        ((HopfIdeal.kerLiftBialgEquiv_apply π hb _).trans
          (HopfIdeal.kerLiftBialgHom_mk π hb x)).symm
    have hcoe : (eπ.symm : H →ₐc[k] _) (π x) = eπ.symm (π x) := rfl
    simp only [f, BialgHom.comp_apply, hcoe, hsymm, Bialgebra.Quotient.liftBialgHom_mk]
  have hfdiff : derivationCompLieHom (B := k) f = ψ := by
    ext d h
    refine DFunLike.congr_fun
      (derivationComp_injective_of_surjective π hb (B := k) ?_) h
    rw [derivationCompLieHom_apply, ← LinearMap.comp_apply, ← derivationComp_comp, hfπ, hdiff d]
  refine ⟨f, hfdiff, fun g hg ↦ ?_⟩
  have hhom :
      (_root_.CommHopfAlgCat.ofHom g : _root_.CommHopfAlgCat.of k H ⟶ K.obj) =
        _root_.CommHopfAlgCat.ofHom f :=
    _root_.CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq _ _ (hg.trans hfdiff.symm)
  exact congrArg _root_.CommHopfAlgCat.Hom.hom hhom

end CommHopfAlgCat

end TauCeti
