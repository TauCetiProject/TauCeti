/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.HopfAlgebra.HopfIdeal

/-!
# The quotient Hopf algebra of a Hopf ideal

For a Hopf algebra `H` over a commutative semiring `R` and a Hopf ideal `I` of `H`, this file
equips the quotient ring `H ⧸ I` with the structure of a Hopf algebra over `R`, descending the
comultiplication, counit and antipode from `H`. The quotient map `H →ₐ[R] H ⧸ I` is exported
as a bialgebra morphism by construction.

This is the Layer 3 milestone "the quotient Hopf algebra `A/I`" of the reductive-groups
roadmap: closed subgroup schemes of an affine group scheme are represented on coordinate
rings by exactly these quotient Hopf algebras, and the three Hopf-ideal closure conditions
(`comul (I) ⊆ I ⊗ H + H ⊗ I`, `counit (I) = 0`, `S(I) ⊆ I`) are precisely what is needed for
the structure maps to descend.

The construction only uses the *easy* direction of the kernel computation for tensor products:
the comultiplication descends because `comul x` lands in `I ⊗ H + H ⊗ I`, which the quotient
map kills. No exactness or flatness input is needed; that is what the Hopf-ideal axioms buy.

## Main definitions

* `TauCeti.HopfIdeal.quotientComulAlgHom`, `TauCeti.HopfIdeal.quotientCounitAlgHom`: the
  comultiplication and counit of the quotient, as `R`-algebra homomorphisms descended from `H`.
* `TauCeti.HopfIdeal.instCoalgebraQuotient`, `instBialgebraQuotient`,
  `instHopfAlgebraQuotient`: the coalgebra, bialgebra and Hopf algebra structures on `H ⧸ I`.
* `TauCeti.HopfIdeal.mkBialgHom`: the quotient map `H →ₐc[R] H ⧸ I` as a bialgebra morphism.
* `TauCeti.HopfIdeal.liftBialgHom`: the bialgebra morphism induced from a bialgebra morphism
  which kills the Hopf ideal.

## References

This follows the standard construction of the quotient Hopf algebra; see Sweedler,
*Hopf Algebras*, Chapter 4, and Waterhouse, *Introduction to Affine Group Schemes*, §16. It
builds on the `TauCeti.HopfIdeal` API and Mathlib's algebra-quotient lift `Ideal.Quotient.liftₐ`,
the tensor-product algebra map `Algebra.TensorProduct.map`, and the bialgebra/Hopf-algebra
constructors `Bialgebra.mk'` and the `HopfAlgebra` axioms. It also uses Mathlib's
`HopfAlgebra.antipodeAlgHom` from `Mathlib.RingTheory.HopfAlgebra.Convolution`, due to
Yaël Dillies, Michał Mrugała and Yunzhou Xie.
-/

open scoped TensorProduct

namespace TauCeti

namespace HopfIdeal

universe u v

variable {R : Type u} {H : Type v}
variable [CommSemiring R]

section Ring

variable [Ring H] [HopfAlgebra R H]
variable (I : HopfIdeal R H)

/-- The tensor square of the quotient map, `H ⊗ H →ₐ[R] (H ⧸ I) ⊗ (H ⧸ I)`. -/
private noncomputable abbrev mkₐ₂ :
    H ⊗[R] H →ₐ[R] (H ⧸ I.toIdeal) ⊗[R] (H ⧸ I.toIdeal) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal) (Ideal.Quotient.mkₐ R I.toIdeal)

private theorem mkₐ₂_includeLeft_eq_zero {y : H} (hy : y ∈ I.toIdeal) :
    mkₐ₂ I (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H) y) =
      0 := by
  rw [Algebra.TensorProduct.includeLeft_apply (R := R) (S := R), Algebra.TensorProduct.map_tmul,
    map_one,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hy, TensorProduct.zero_tmul]

private theorem mkₐ₂_includeRight_eq_zero {y : H} (hy : y ∈ I.toIdeal) :
    mkₐ₂ I (Algebra.TensorProduct.includeRight y) = 0 := by
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hy, TensorProduct.tmul_zero]

/-- The tensor square of the quotient map kills `I ⊗ H + H ⊗ I`. -/
private theorem leSup_le_ker_mkₐ₂ :
    leftTensorIdeal (R := R) (H := H) I.toIdeal ⊔ rightTensorIdeal (R := R) (H := H) I.toIdeal ≤
      RingHom.ker (mkₐ₂ I).toRingHom := by
  apply sup_le
  · rw [leftTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact mkₐ₂_includeLeft_eq_zero I hy
  · rw [rightTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact mkₐ₂_includeRight_eq_zero I hy

/-- The comultiplication of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
noncomputable def quotientComulAlgHom :
    (H ⧸ I.toIdeal) →ₐ[R] (H ⧸ I.toIdeal) ⊗[R] (H ⧸ I.toIdeal) :=
  Ideal.Quotient.liftₐ I.toIdeal ((mkₐ₂ I).comp (Bialgebra.comulAlgHom R H)) <| by
    intro x hx
    rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    exact RingHom.mem_ker.mp (leSup_le_ker_mkₐ₂ I (I.comul_mem (mem_toIdeal.mp hx)))

/-- The counit of the quotient, as an `R`-algebra homomorphism descended from `H`. -/
noncomputable def quotientCounitAlgHom : (H ⧸ I.toIdeal) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I.toIdeal (Bialgebra.counitAlgHom R H) <| by
    intro x hx
    rw [Bialgebra.counitAlgHom_apply]
    exact I.counit_eq_zero (mem_toIdeal.mp hx)

private theorem quotientComulAlgHom_comp_mkₐ :
    (quotientComulAlgHom I).comp (Ideal.Quotient.mkₐ R I.toIdeal) =
      (mkₐ₂ I).comp (Bialgebra.comulAlgHom R H) := by
  rw [quotientComulAlgHom]
  exact Ideal.Quotient.liftₐ_comp I.toIdeal _ _

private theorem quotientCounitAlgHom_comp_mkₐ :
    (quotientCounitAlgHom I).comp (Ideal.Quotient.mkₐ R I.toIdeal) =
      Bialgebra.counitAlgHom R H := by
  rw [quotientCounitAlgHom]
  exact Ideal.Quotient.liftₐ_comp I.toIdeal _ _

/-- The descended comultiplication, evaluated on a quotient class. -/
@[simp]
theorem quotientComulAlgHom_mk (h : H) :
    quotientComulAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h)
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal)
        (Ideal.Quotient.mkₐ R I.toIdeal) (Coalgebra.comul h) := by
  exact AlgHom.congr_fun (quotientComulAlgHom_comp_mkₐ I) h

/-- The descended counit, evaluated on a quotient class. -/
@[simp]
theorem quotientCounitAlgHom_mk (h : H) :
    quotientCounitAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h := by
  exact AlgHom.congr_fun (quotientCounitAlgHom_comp_mkₐ I) h

/-- The underlying linear quotient map `H →ₗ[R] H ⧸ I`. -/
private noncomputable abbrev mkL : H →ₗ[R] H ⧸ I.toIdeal :=
  (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

private theorem mkL_surjective : Function.Surjective (mkL I) :=
  Ideal.Quotient.mkₐ_surjective R I.toIdeal

private theorem comul_mkL_apply (h : H) :
    (quotientComulAlgHom I).toLinearMap (mkL I h)
      = TensorProduct.map (mkL I) (mkL I) (Coalgebra.comul h) := by
  calc
    (quotientComulAlgHom I).toLinearMap (mkL I h)
        = quotientComulAlgHom I (Ideal.Quotient.mkₐ R I.toIdeal h) := rfl
    _ = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal)
        (Ideal.Quotient.mkₐ R I.toIdeal) (Coalgebra.comul h) :=
      quotientComulAlgHom_mk I h
    _ = TensorProduct.map (mkL I) (mkL I) (Coalgebra.comul h) :=
      LinearMap.congr_fun
        (Algebra.TensorProduct.toLinearMap_map (Ideal.Quotient.mkₐ R I.toIdeal)
          (Ideal.Quotient.mkₐ R I.toIdeal)) _

/-- The quotient comultiplication intertwines `mkL` with the comultiplication of `H`. -/
private theorem comul_comp_mkL :
    (quotientComulAlgHom I).toLinearMap ∘ₗ mkL I
      = TensorProduct.map (mkL I) (mkL I) ∘ₗ Coalgebra.comul := by
  ext h
  simpa only [LinearMap.comp_apply] using comul_mkL_apply I h

/-- The quotient counit intertwines `mkL` with the counit of `H`. -/
private theorem counit_comp_mkL :
    (quotientCounitAlgHom I).toLinearMap ∘ₗ mkL I = Coalgebra.counit (R := R) := by
  ext h
  exact quotientCounitAlgHom_mk I h

/-- A linear map out of the quotient is determined by its precomposition with `mkL`. -/
private theorem linearMap_ext {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : (H ⧸ I.toIdeal) →ₗ[R] N} (hfg : f ∘ₗ mkL I = g ∘ₗ mkL I) : f = g := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨a, rfl⟩ := mkL_surjective I q
  exact LinearMap.congr_fun hfg a

/-- The coalgebra structure on the quotient, with comultiplication and counit descended from
`H`. -/
noncomputable instance instCoalgebraQuotient : Coalgebra R (H ⧸ I.toIdeal) where
  comul := (quotientComulAlgHom I).toLinearMap
  counit := (quotientCounitAlgHom I).toLinearMap
  coassoc := by
    refine linearMap_ext I (LinearMap.ext fun h => ?_)
    -- Transport coassociativity across the surjective quotient map `mkL`; the simp set
    -- evaluates only the quotient-map naturality lemmas for tensoring linear maps.
    simp only [LinearMap.comp_apply, comul_mkL_apply, LinearMap.rTensor_map, LinearMap.lTensor_map,
      comul_comp_mkL, ← LinearMap.map_rTensor, ← LinearMap.map_lTensor]
    exact (TensorProduct.map_map_assoc (mkL I) (mkL I) (mkL I) _).symm.trans
      (congrArg _ (Coalgebra.coassoc_apply h))
  rTensor_counit_comp_comul := by
    refine linearMap_ext I ?_
    rw [LinearMap.comp_assoc, comul_comp_mkL, ← LinearMap.comp_assoc, LinearMap.rTensor_comp_map,
      counit_comp_mkL, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc,
      Coalgebra.rTensor_counit_comp_comul]
    ext h
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul]
  lTensor_counit_comp_comul := by
    refine linearMap_ext I ?_
    rw [LinearMap.comp_assoc, comul_comp_mkL, ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map,
      counit_comp_mkL, ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc,
      Coalgebra.lTensor_counit_comp_comul]
    ext h
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul]

/-- The comultiplication on the quotient, evaluated on a quotient class. -/
@[simp]
theorem comul_mk (h : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h)
      = TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
        (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Coalgebra.comul h) :=
  comul_mkL_apply I h

/-- The counit on the quotient, evaluated on a quotient class. -/
@[simp]
theorem counit_mk (h : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Coalgebra.counit (R := R) h :=
  quotientCounitAlgHom_mk I h

/-- The bialgebra structure on the quotient, whose coalgebra structure maps are algebra
homomorphisms. -/
noncomputable instance instBialgebraQuotient : Bialgebra R (H ⧸ I.toIdeal) :=
  Bialgebra.mk' R (H ⧸ I.toIdeal)
    (map_one (quotientCounitAlgHom I))
    (fun {a b} => map_mul (quotientCounitAlgHom I) a b)
    (map_one (quotientComulAlgHom I))
    (fun {a b} => map_mul (quotientComulAlgHom I) a b)

/-- The antipode of the quotient, as an `R`-linear map descended from `H`. -/
noncomputable def quotientAntipodeLinearMap : (H ⧸ I.toIdeal) →ₗ[R] H ⧸ I.toIdeal where
  toFun q :=
    Quotient.liftOn' q
      (fun h : H => Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h)) <| by
        intro a b hab
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, ← map_sub]
        exact I.antipode_mem (by simpa [Submodule.quotientRel_def] using hab)
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    -- Quotient induction reduces the linearity goals to the representative formula used in
    -- `toFun`; the remaining proof is just linearity of the original antipode and quotient map.
    change Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R (a + b)) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R a) +
        Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R b)
    rw [map_add, map_add]
  map_smul' := by
    intro r
    rintro ⟨a⟩
    -- As above, this exposes the representative-level formula after quotient induction.
    change Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R (r • a)) =
      r • Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R a)
    rw [map_smul, map_smul]

/-- The descended antipode linear map, evaluated on a quotient class. -/
@[simp]
theorem quotientAntipodeLinearMap_mk (h : H) :
    quotientAntipodeLinearMap I (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) := by
  rfl

@[simp]
private theorem antipode_comp_mkL :
    quotientAntipodeLinearMap I ∘ₗ mkL I = mkL I ∘ₗ HopfAlgebra.antipode R := by
  ext h
  exact quotientAntipodeLinearMap_mk I h

/-- Multiplication on the quotient is the transport of multiplication on `H`: this is the
naturality of `LinearMap.mul'` along the algebra homomorphism `mkL`. -/
private theorem mul'_comp_map_mkL :
    LinearMap.mul' R (H ⧸ I.toIdeal) ∘ₗ TensorProduct.map (mkL I) (mkL I)
      = mkL I ∘ₗ LinearMap.mul' R H := by
  refine TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    AlgHom.toLinearMap_apply, map_mul]

private theorem mul'_map_mkL_apply (x : H ⊗[R] H) :
    LinearMap.mul' R (H ⧸ I.toIdeal) (TensorProduct.map (mkL I) (mkL I) x)
      = mkL I (LinearMap.mul' R H x) :=
  LinearMap.congr_fun (mul'_comp_map_mkL I) x

/-- The Hopf algebra structure on the quotient, with antipode descended from `H`. -/
noncomputable instance instHopfAlgebraQuotient : HopfAlgebra R (H ⧸ I.toIdeal) where
  antipode := quotientAntipodeLinearMap I
  mul_antipode_rTensor_comul := by
    refine linearMap_ext I (LinearMap.ext fun h => ?_)
    -- The Hopf identities are transported along `mkL`: first evaluate quotient structure maps
    -- on representatives, then use the corresponding identity in `H`.
    simp only [LinearMap.comp_apply, comul_mk, LinearMap.rTensor_map, antipode_comp_mkL,
      ← LinearMap.map_rTensor, mul'_map_mkL_apply, HopfAlgebra.mul_antipode_rTensor_comul_apply,
      AlgHom.toLinearMap_apply, AlgHom.commutes, Algebra.linearMap_apply, counit_mk]
  mul_antipode_lTensor_comul := by
    refine linearMap_ext I (LinearMap.ext fun h => ?_)
    -- Same transport argument for the left tensor version of the antipode identity.
    simp only [LinearMap.comp_apply, comul_mk, LinearMap.lTensor_map, antipode_comp_mkL,
      ← LinearMap.map_lTensor, mul'_map_mkL_apply, HopfAlgebra.mul_antipode_lTensor_comul_apply,
      AlgHom.toLinearMap_apply, AlgHom.commutes, Algebra.linearMap_apply, counit_mk]

/-- The antipode on the quotient, evaluated on a quotient class. -/
@[simp]
theorem antipode_mk (h : H) :
    HopfAlgebra.antipode R (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R I.toIdeal (HopfAlgebra.antipode R h) :=
  quotientAntipodeLinearMap_mk I h

/-- The quotient map `H →ₐ[R] H ⧸ I` as a bialgebra morphism: it is an algebra homomorphism
respecting the counit and comultiplication by construction. -/
noncomputable def mkBialgHom : H →ₐc[R] H ⧸ I.toIdeal :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I.toIdeal)
    (by ext h; simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, counit_mk])
    (by
      ext h
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comul_mk]
      exact LinearMap.congr_fun
        (Algebra.TensorProduct.toLinearMap_map (Ideal.Quotient.mkₐ R I.toIdeal)
          (Ideal.Quotient.mkₐ R I.toIdeal)) _)

/-- The quotient bialgebra morphism, evaluated on an element of `H`. -/
@[simp]
theorem mkBialgHom_apply (h : H) : mkBialgHom I h = Ideal.Quotient.mkₐ R I.toIdeal h := rfl

variable {K : Type*} [Semiring K] [Bialgebra R K]

private theorem liftBialgHom_kill (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) {h : H} (hh : h ∈ I.toIdeal) :
    (f : H →ₐ[R] K) h = 0 :=
  RingHom.mem_ker.mp (show h ∈ RingHom.ker f.toAlgHom.toRingHom from hf hh)

private theorem liftBialgHomAlg_mk (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    Ideal.Quotient.liftₐ I.toIdeal (f : H →ₐ[R] K)
      (fun _ ha => liftBialgHom_kill I f hf ha) (Ideal.Quotient.mkₐ R I.toIdeal h) =
        f h := by
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk]
  rfl

/-- A bialgebra morphism out of `H` which kills a Hopf ideal factors through the quotient
bialgebra. -/
noncomputable def liftBialgHom (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ I.toIdeal →ₐc[R] K :=
  BialgHom.ofAlgHom
    (Ideal.Quotient.liftₐ I.toIdeal (f : H →ₐ[R] K)
      fun a ha => liftBialgHom_kill I f hf ha)
    (by
      ext q
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
      rw [AlgHom.comp_apply, liftBialgHomAlg_mk I f hf h, Bialgebra.counitAlgHom_apply,
        Bialgebra.counitAlgHom_apply]
      -- After quotient-surjectivity reduction, `BialgHom.ofAlgHom` leaves the same counit
      -- equality with the two sides presented through different wrapper APIs.
      change Coalgebra.counit (R := R) (f h) =
        Coalgebra.counit (R := R) (Ideal.Quotient.mkₐ R I.toIdeal h)
      rw [counit_mk]
      exact CoalgHomClass.counit_comp_apply f h)
    (by
      ext q
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
      let F : H ⧸ I.toIdeal →ₐ[R] K :=
        Ideal.Quotient.liftₐ I.toIdeal (f : H →ₐ[R] K)
          fun a ha => liftBialgHom_kill I f hf ha
      have hF_mk (x : H) : F (Ideal.Quotient.mkₐ R I.toIdeal x) = f x :=
        liftBialgHomAlg_mk I f hf x
      have hF_comp :
          F.toLinearMap.comp (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap = f.toLinearMap := by
        ext x
        exact hF_mk x
      -- These two `change`s expose the bialgebra-hom comultiplication equation and then the
      -- underlying linear tensor-map equation after evaluating at a quotient representative.
      change ((Algebra.TensorProduct.map F F).comp (Bialgebra.comulAlgHom R (H ⧸ I.toIdeal)))
          (Ideal.Quotient.mkₐ R I.toIdeal h) =
        ((Bialgebra.comulAlgHom R K).comp F) (Ideal.Quotient.mkₐ R I.toIdeal h)
      change (Algebra.TensorProduct.map F F)
          (Bialgebra.comulAlgHom R (H ⧸ I.toIdeal) (Ideal.Quotient.mkₐ R I.toIdeal h)) =
        Bialgebra.comulAlgHom R K (F (Ideal.Quotient.mkₐ R I.toIdeal h))
      rw [Bialgebra.comulAlgHom_apply, hF_mk, Bialgebra.comulAlgHom_apply, comul_mk]
      change TensorProduct.map F.toLinearMap F.toLinearMap
          (TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
            (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Coalgebra.comul h)) =
        Coalgebra.comul (R := R) (f h)
      rw [TensorProduct.map_map, hF_comp]
      exact CoalgHomClass.map_comp_comul_apply f h)

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
    (liftBialgHom I f hf).comp (mkBialgHom I) = f := by
  ext h
  change liftBialgHom I f hf (mkBialgHom I h) = f h
  rw [mkBialgHom_apply, liftBialgHom_mk]

/-- A bialgebra morphism out of the quotient is determined by its precomposition with the
quotient map. -/
theorem liftBialgHom_unique (f : H →ₐc[R] K)
    (hf : I.toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom) (g : H ⧸ I.toIdeal →ₐc[R] K)
    (hg : g.comp (mkBialgHom I) = f) :
    g = liftBialgHom I f hf := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  calc
    g (Ideal.Quotient.mkₐ R I.toIdeal h) = (g.comp (mkBialgHom I)) h := rfl
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
