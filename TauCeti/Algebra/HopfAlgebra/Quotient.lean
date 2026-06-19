/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.HopfAlgebra.HopfIdeal

/-!
# The quotient Hopf algebra of a Hopf ideal

For a Hopf algebra `H` over a commutative ring `R` and a Hopf ideal `I` of `H`, Mathlib equips the
quotient ring `H ⧸ I` with the structure of a Hopf algebra over `R`, descending the
comultiplication, counit and antipode from `H` (see
`Mathlib.RingTheory.{Coalgebra,Bialgebra,HopfAlgebra}.Quotient`). Mathlib's instances fire on an
`Ideal` once it is known to be two-sided, a coideal, and antipode-stable. This file supplies the
**bridge** turning a `TauCeti.HopfIdeal` into those Mathlib hypotheses, so that Mathlib's
`Coalgebra`/`Bialgebra`/`HopfAlgebra` instances apply to `H ⧸ I.toIdeal`; on top of that bridge it
provides the parts Mathlib lacks: the **universal property** `liftBialgHom` of the quotient
bialgebra, and the antipode of the quotient packaged as an algebra homomorphism
`quotientAntipodeAlgHom` in the commutative case.

This is the Layer 3 milestone "the quotient Hopf algebra `A/I`" of the reductive-groups
roadmap: closed subgroup schemes of an affine group scheme are represented on coordinate
rings by exactly these quotient Hopf algebras, and the three Hopf-ideal closure conditions
(`comul (I) ⊆ I ⊗ H + H ⊗ I`, `counit (I) = 0`, `S(I) ⊆ I`) are precisely what is needed for
the structure maps to descend.

## Main definitions

* `TauCeti.HopfIdeal.instIsCoideal`, `TauCeti.HopfIdeal.instIsHopfIdeal`: the bridge instances
  exhibiting `I.toIdeal` as a coideal and a Hopf ideal in Mathlib's sense, so that Mathlib's
  quotient coalgebra/bialgebra/Hopf instances fire on `H ⧸ I.toIdeal`.
* `TauCeti.HopfIdeal.liftBialgHom`: the bialgebra morphism induced from a bialgebra morphism
  which kills the Hopf ideal, together with its computation and uniqueness lemmas.
* `TauCeti.HopfIdeal.quotientAntipodeAlgHom`: the antipode of the quotient as an `R`-algebra
  homomorphism, valid when `H` is commutative.

The quotient coalgebra/bialgebra/Hopf-algebra structure maps and the quotient bialgebra morphism
themselves are Mathlib's `Bialgebra.Quotient.comulAlgHom`, `Bialgebra.Quotient.counitAlgHom`,
`Bialgebra.Quotient.mkBialgHom`, and `HopfAlgebra.antipode`; the older TauCeti names for them are
retained as deprecated wrappers.

## References

This follows the standard construction of the quotient Hopf algebra; see Sweedler,
*Hopf Algebras*, Chapter 4, and Waterhouse, *Introduction to Affine Group Schemes*, §16. It
builds on the `TauCeti.HopfIdeal` API and Mathlib's quotient Hopf-algebra machinery
(`Mathlib.RingTheory.HopfAlgebra.Quotient`, due to Robert Hawkins), the algebra-quotient lift
`Ideal.Quotient.liftₐ`, and `HopfAlgebra.antipodeAlgHom` from
`Mathlib.RingTheory.HopfAlgebra.Convolution`, due to Yaël Dillies, Michał Mrugała and Yunzhou Xie.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfIdeal

universe u v

variable {R : Type u} {H : Type v}
variable [CommRing R]

section Ring

variable [Ring H] [HopfAlgebra R H]

/-- TauCeti's `leftTensorIdeal I` (`I ⊗ H`), viewed as an `R`-submodule, is the range of
`rTensor H (I.restrictScalars R).subtype`. This is Mathlib's `Ideal.map_includeLeft_eq`. -/
theorem leftTensorIdeal_restrictScalars_eq_range (I : Ideal H) :
    (leftTensorIdeal (R := R) (H := H) I).restrictScalars R =
      LinearMap.range (LinearMap.rTensor H (I.restrictScalars R).subtype) :=
  Ideal.map_includeLeft_eq (R := R) (A := H) (B := H) I

/-- TauCeti's `rightTensorIdeal I` (`H ⊗ I`), viewed as an `R`-submodule, is the range of
`lTensor H (I.restrictScalars R).subtype`. This is Mathlib's `Ideal.map_includeRight_eq`. -/
theorem rightTensorIdeal_restrictScalars_eq_range (I : Ideal H) :
    (rightTensorIdeal (R := R) (H := H) I).restrictScalars R =
      LinearMap.range (LinearMap.lTensor H (I.restrictScalars R).subtype) :=
  Ideal.map_includeRight_eq (R := R) (A := H) (B := H) I

/-- The bridge: TauCeti's `I ⊗ H + H ⊗ I` (a sup of ideals of `H ⊗[R] H`), viewed as an
`R`-submodule, equals Mathlib's coideal target `range (lTensor …) ⊔ range (rTensor …)`. -/
theorem leftTensorIdeal_sup_eq_range (I : Ideal H) :
    (leftTensorIdeal (R := R) (H := H) I ⊔ rightTensorIdeal (R := R) (H := H) I).restrictScalars R =
      LinearMap.range (LinearMap.lTensor H (I.restrictScalars R).subtype) ⊔
        LinearMap.range (LinearMap.rTensor H (I.restrictScalars R).subtype) := by
  rw [Submodule.restrictScalars_sup, leftTensorIdeal_restrictScalars_eq_range,
    rightTensorIdeal_restrictScalars_eq_range, sup_comm]

/-- A `HopfIdeal` gives Mathlib's coideal structure on the underlying `R`-submodule, so that
Mathlib's quotient `Coalgebra`/`Bialgebra` instances fire on `H ⧸ I.toIdeal`. -/
instance instIsCoideal (I : HopfIdeal R H) :
    (I.toIdeal.restrictScalars R).IsCoideal := by
  rw [Submodule.isCoideal_iff_comul_mem]
  refine ⟨fun _ hx => I.counit_eq_zero hx, fun _ hx => ?_⟩
  have := I.comul_mem hx
  rwa [← Submodule.restrictScalars_mem R, leftTensorIdeal_sup_eq_range] at this

/-- A `HopfIdeal` gives Mathlib's `Ideal.IsHopfIdeal`, so that Mathlib's quotient
`HopfAlgebra` instance fires on `H ⧸ I.toIdeal`. -/
instance instIsHopfIdeal (I : HopfIdeal R H) : I.toIdeal.IsHopfIdeal R where
  __ := instIsCoideal I
  antipode_mem := fun _ hx => I.antipode_mem hx

variable (I : HopfIdeal R H)

/-- The comultiplication of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
@[deprecated Bialgebra.Quotient.comulAlgHom (since := "2026-06-19")]
noncomputable def quotientComulAlgHom :
    (H ⧸ I.toIdeal) →ₐ[R] (H ⧸ I.toIdeal) ⊗[R] (H ⧸ I.toIdeal) :=
  Bialgebra.Quotient.comulAlgHom I.toIdeal

/-- The counit of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
@[deprecated Bialgebra.Quotient.counitAlgHom (since := "2026-06-19")]
noncomputable def quotientCounitAlgHom : (H ⧸ I.toIdeal) →ₐ[R] R :=
  Bialgebra.Quotient.counitAlgHom I.toIdeal

/-- The comultiplication on the quotient, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.comul_mk (since := "2026-06-19")]
theorem comul_mk (h : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h)
      = TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
        (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Coalgebra.comul h) := by
  rw [Ideal.Quotient.mkₐ_eq_mk]
  exact Bialgebra.Quotient.comul_mk I.toIdeal h

/-- The counit on the quotient, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.counit_mk (since := "2026-06-19")]
theorem counit_mk (h : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h := by
  rw [Ideal.Quotient.mkₐ_eq_mk]
  exact Bialgebra.Quotient.counit_mk I.toIdeal h

/-- The descended comultiplication, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.comul_mk (since := "2026-06-19")]
theorem quotientComulAlgHom_mk (h : H) :
    quotientComulAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h)
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal)
        (Ideal.Quotient.mkₐ R I.toIdeal) (Coalgebra.comul h) := by
  rw [quotientComulAlgHom, Ideal.Quotient.mkₐ_eq_mk]
  refine (Bialgebra.Quotient.comul_mk I.toIdeal h).trans ?_
  exact (LinearMap.congr_fun
    (Algebra.TensorProduct.toLinearMap_map (Ideal.Quotient.mkₐ R I.toIdeal)
      (Ideal.Quotient.mkₐ R I.toIdeal)) _).symm

/-- The descended counit, evaluated on a quotient class. -/
@[deprecated Bialgebra.Quotient.counit_mk (since := "2026-06-19")]
theorem quotientCounitAlgHom_mk (h : H) :
    quotientCounitAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h := by
  rw [quotientCounitAlgHom, Ideal.Quotient.mkₐ_eq_mk]
  exact Bialgebra.Quotient.counit_mk I.toIdeal h

/-- The antipode of the quotient, as an `R`-linear map descended from `H`. -/
@[deprecated "Use `HopfAlgebra.antipode R` on the quotient instead." (since := "2026-06-19")]
noncomputable def quotientAntipodeLinearMap : (H ⧸ I.toIdeal) →ₗ[R] H ⧸ I.toIdeal :=
  HopfAlgebra.antipode R

/-- The antipode on the quotient, evaluated on a quotient class. -/
@[deprecated HopfAlgebra.Quotient.antipode_mk (since := "2026-06-19")]
theorem antipode_mk (h : H) :
    HopfAlgebra.antipode R (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  rw [Ideal.Quotient.mkₐ_eq_mk]
  exact HopfAlgebra.Quotient.antipode_mk I.toIdeal h

/-- The descended antipode linear map, evaluated on a quotient class. -/
@[deprecated HopfAlgebra.Quotient.antipode_mk (since := "2026-06-19")]
theorem quotientAntipodeLinearMap_mk (h : H) :
    quotientAntipodeLinearMap I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  rw [quotientAntipodeLinearMap, Ideal.Quotient.mkₐ_eq_mk]
  exact HopfAlgebra.Quotient.antipode_mk I.toIdeal h

/-- The quotient map `H →ₐ[R] H ⧸ I` as a bialgebra morphism: it is an algebra homomorphism
respecting the counit and comultiplication by construction. -/
@[deprecated Bialgebra.Quotient.mkBialgHom (since := "2026-06-19")]
noncomputable def mkBialgHom : H →ₐc[R] H ⧸ I.toIdeal :=
  Bialgebra.Quotient.mkBialgHom I.toIdeal

/-- The quotient bialgebra morphism, evaluated on an element of `H`. -/
@[deprecated Bialgebra.Quotient.mkBialgHom_apply (since := "2026-06-19")]
theorem mkBialgHom_apply (h : H) : mkBialgHom I h = Ideal.Quotient.mkₐ R I.toIdeal h := by
  rw [mkBialgHom, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk]

variable {K : Type*} [Semiring K] [Bialgebra R K]

private theorem liftBialgHom_kill (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) {h : H} (hh : h ∈ I.toIdeal) :
    (f : H →ₐ[R] K) h = 0 :=
  RingHom.mem_ker.mp (hf hh)

private noncomputable abbrev liftBialgHomAlg (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ I.toIdeal →ₐ[R] K :=
  Ideal.Quotient.liftₐ I.toIdeal (f : H →ₐ[R] K)
    fun _ ha => liftBialgHom_kill I f hf ha

private theorem liftBialgHomAlg_mk (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    liftBialgHomAlg I f hf (Ideal.Quotient.mkₐ R I.toIdeal h) = f h := by
  exact AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp I.toIdeal (f : H →ₐ[R] K)
      fun _ ha => liftBialgHom_kill I f hf ha) h

private theorem liftBialgHomAlg_toLinearMap_comp_mkₐ (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (liftBialgHomAlg I f hf).toLinearMap.comp
      (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap = f.toLinearMap := by
  ext h
  exact liftBialgHomAlg_mk I f hf h

private theorem liftBialgHomAlg_comul_mk (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    TensorProduct.map (liftBialgHomAlg I f hf).toLinearMap
        (liftBialgHomAlg I f hf).toLinearMap
        (TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
          (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Coalgebra.comul h)) =
      Coalgebra.comul (R := R) (f h) := by
  rw [TensorProduct.map_map, liftBialgHomAlg_toLinearMap_comp_mkₐ]
  exact CoalgHomClass.map_comp_comul_apply f h

/-- A bialgebra morphism out of `H` which kills a Hopf ideal factors through the quotient
bialgebra. -/
noncomputable def liftBialgHom (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ I.toIdeal →ₐc[R] K :=
  BialgHom.ofAlgHom
    (liftBialgHomAlg I f hf)
    (by
      ext q
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
      rw [AlgHom.comp_apply, liftBialgHomAlg_mk I f hf h, Bialgebra.counitAlgHom_apply,
        Bialgebra.counitAlgHom_apply]
      -- After quotient-surjectivity reduction, `BialgHom.ofAlgHom` leaves the same counit
      -- equality with the two sides presented through different wrapper APIs.
      change Coalgebra.counit (R := R) (f h) =
        Coalgebra.counit (R := R) (Ideal.Quotient.mk I.toIdeal h)
      rw [Bialgebra.Quotient.counit_mk]
      exact CoalgHomClass.counit_comp_apply f h)
    (by
      ext q
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        liftBialgHomAlg_mk I f hf h, Bialgebra.comulAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
        Bialgebra.Quotient.comul_mk]
      exact liftBialgHomAlg_comul_mk I f hf h)

/-- The quotient lift, evaluated on a quotient class. -/
@[simp]
theorem liftBialgHom_mk (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    liftBialgHom I f hf (Ideal.Quotient.mkₐ R I.toIdeal h) = f h := by
  rw [liftBialgHom]
  exact liftBialgHomAlg_mk I f hf h

/-- The quotient lift composed with the quotient map is the original bialgebra morphism. -/
@[simp]
theorem liftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (liftBialgHom I f hf).comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) = f := by
  ext h
  rw [BialgHom.comp_apply, Bialgebra.Quotient.mkBialgHom_apply,
    ← Ideal.Quotient.mkₐ_eq_mk (R₁ := R), liftBialgHom_mk]

/-- A bialgebra morphism out of the quotient is determined by its precomposition with the
quotient map. -/
theorem liftBialgHom_unique (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (g : H ⧸ I.toIdeal →ₐc[R] K)
    (hg : g.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) = f) :
    g = liftBialgHom I f hf := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  calc
    g (Ideal.Quotient.mkₐ R I.toIdeal h)
        = (g.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal)) h := by
          rw [BialgHom.comp_apply, Bialgebra.Quotient.mkBialgHom_apply,
            Ideal.Quotient.mkₐ_eq_mk (R₁ := R)]
    _ = f h := BialgHom.congr_fun hg h
    _ = liftBialgHom I f hf (Ideal.Quotient.mkₐ R I.toIdeal h) :=
      (liftBialgHom_mk I f hf h).symm

end Ring

section CommRing

variable [CommRing H] [HopfAlgebra R H]
variable (I : HopfIdeal R H)

/-- The antipode of the quotient, as an `R`-algebra homomorphism descended from `H` (valid since
`H` is commutative, where the antipode is an algebra homomorphism). -/
noncomputable def quotientAntipodeAlgHom : (H ⧸ I.toIdeal) →ₐ[R] H ⧸ I.toIdeal :=
  Ideal.Quotient.liftₐ I.toIdeal
    ((Ideal.Quotient.mkₐ R I.toIdeal).comp (HopfAlgebra.antipodeAlgHom R H)) <| by
    intro x hx
    rw [AlgHom.comp_apply, HopfAlgebra.antipodeAlgHom_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.antipode_mem (mem_toIdeal.mp hx))

private theorem quotientAntipodeAlgHom_comp_mkₐ :
    (quotientAntipodeAlgHom I).comp (Ideal.Quotient.mkₐ R I.toIdeal) =
      (Ideal.Quotient.mkₐ R I.toIdeal).comp (HopfAlgebra.antipodeAlgHom R H) := by
  rw [quotientAntipodeAlgHom]
  exact Ideal.Quotient.liftₐ_comp I.toIdeal _ _

/-- The descended antipode algebra homomorphism, evaluated on a quotient class. -/
@[simp]
theorem quotientAntipodeAlgHom_mk (h : H) :
    quotientAntipodeAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  exact AlgHom.congr_fun (quotientAntipodeAlgHom_comp_mkₐ I) h

end CommRing

end HopfIdeal

end TauCeti
