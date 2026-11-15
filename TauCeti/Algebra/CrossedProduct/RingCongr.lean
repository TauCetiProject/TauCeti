/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.CrossedProduct.Basic

/-!
# Crossed products across different base rings

A compatible isomorphism of coefficient rings and automorphism groups identifies the
crossed-product rings, even when their base rings live in different universes. The map
is coefficientwise and reindexes the crossed-product basis. It works for unnormalized
cocycles and requires neither finiteness nor a Galois hypothesis.

`comapRingEquiv` supplies the algebraic transport needed when identifying crossed products
formed using different presentations of a field and its finite normal extensions. The
coefficient and basis formulas specify the map independently of cohomology. The scalar
compatibility theorem records how the two base rings act. `scalarExtensionEquiv` then
identifies the tensor-defined scalar extension with the transported crossed product, with
explicit pure-tensor, coefficient and basis formulas.

The coordinate construction previously used for `CrossedProduct.congr` and
`CrossedProduct.uliftEquiv` is generalized here, using Mathlib's `Finsupp.domCongr`
and `Finsupp.mapRange.addEquiv`.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public noncomputable section

universe u v w z

namespace TauCeti.CrossedProduct

variable {K : Type u} [CommSemiring K] {L : Type v} [CommRing L] [Algebra K L]
  {R : Type w} [CommSemiring R] {M : Type z} [CommRing M] [Algebra R M]
  (c : TwoCocycle K L) (ι : L ≃+* M) (π : (M ≃ₐ[R] M) ≃* (L ≃ₐ[K] L))
  (hπ : ∀ g x, ι (π g x) = g (ι x))

private def comapAddEquiv : CrossedProduct (c.comap (R := R) π ι hπ) ≃+ CrossedProduct c :=
  (basis _).repr.toAddEquiv.trans
    ((Finsupp.domCongr π.toEquiv).trans
      ((Finsupp.mapRange.addEquiv ι.symm.toAddEquiv).trans (basis c).repr.symm.toAddEquiv))

private theorem comapAddEquiv_smul_basis (g : M ≃ₐ[R] M) (x : M) :
    comapAddEquiv c ι π hπ (x • basis _ g) = ι.symm x • basis c (π g) := by
  simp [comapAddEquiv, Finsupp.smul_single, smul_eq_mul]

/-- Identify the crossed product of a transported cocycle with the original ring.
The coefficient isomorphism and automorphism isomorphism may change the base ring. -/
def comapRingEquiv : CrossedProduct (c.comap (R := R) π ι hπ) ≃+* CrossedProduct c where
  __ := comapAddEquiv c ι π hπ
  map_mul' a b := by
    -- Keep the additive equivalence bundled so its additive laws apply during induction.
    change comapAddEquiv c ι π hπ (a * b) =
      comapAddEquiv c ι π hπ a * comapAddEquiv c ι π hπ b
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
    | smul_basis g x =>
      induction b using induction_on with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
      | smul_basis h y =>
        have hact : ι.symm (g y) = π g (ι.symm y) := by
          apply ι.injective
          simp [hπ]
        simp [smul_basis_mul_smul_basis, comapAddEquiv_smul_basis,
          TwoCocycle.comap_toFun, hact]

/-- The ring transport reindexes basis vectors by the automorphism isomorphism. -/
@[simp]
theorem comapRingEquiv_basis (g : M ≃ₐ[R] M) :
    comapRingEquiv c ι π hπ (basis _ g) = basis c (π g) := by
  simpa [comapRingEquiv] using comapAddEquiv_smul_basis c ι π hπ g 1

/-- Embedded coefficients are carried by the inverse coefficient isomorphism. -/
@[simp]
theorem comapRingEquiv_inc (x : M) :
    comapRingEquiv c ι π hπ (inc _ x) = inc c (ι.symm x) := by
  simp [inc_apply, comapRingEquiv, comapAddEquiv_smul_basis, TwoCocycle.comap_toFun]

/-- The transport is semilinear for the coefficient-ring actions. -/
@[simp]
theorem comapRingEquiv_smul (x : M) (a : CrossedProduct (c.comap (R := R) π ι hπ)) :
    comapRingEquiv c ι π hπ (x • a) = ι.symm x • comapRingEquiv c ι π hπ a := by
  simp only [smul_def, map_mul, comapRingEquiv_inc]

@[simp]
theorem comapRingEquiv_symm_basis (g : L ≃ₐ[K] L) :
    (comapRingEquiv c ι π hπ).symm (basis c g) = basis _ (π.symm g) := by
  apply (comapRingEquiv c ι π hπ).injective
  simp

@[simp]
theorem comapRingEquiv_symm_inc (x : L) :
    (comapRingEquiv c ι π hπ).symm (inc c x) = inc _ (ι x) := by
  apply (comapRingEquiv c ι π hπ).injective
  simp

/-- The inverse transport is semilinear for the coefficient-ring actions. -/
@[simp]
theorem comapRingEquiv_symm_smul (x : L) (a : CrossedProduct c) :
    (comapRingEquiv c ι π hπ).symm (x • a) =
      ι x • (comapRingEquiv c ι π hπ).symm a := by
  simp only [smul_def, map_mul, comapRingEquiv_symm_inc]

/-- Every coordinate is transported by the specified coefficient isomorphism. -/
@[simp]
theorem repr_comapRingEquiv (a : CrossedProduct (c.comap (R := R) π ι hπ))
    (g : L ≃ₐ[K] L) :
    (basis c).repr (comapRingEquiv c ι π hπ a) g =
      ι.symm ((basis _).repr a (π.symm g)) := by
  simp [comapRingEquiv, comapAddEquiv, Finsupp.domCongr]

/-- Inverse transport maps every coordinate by the coefficient isomorphism. -/
@[simp]
theorem repr_comapRingEquiv_symm (a : CrossedProduct c) (g : M ≃ₐ[R] M) :
    (basis _).repr ((comapRingEquiv c ι π hπ).symm a) g =
      ι ((basis c).repr a (π g)) := by
  apply ι.symm.injective
  simpa using (repr_comapRingEquiv c ι π hπ
    ((comapRingEquiv c ι π hπ).symm a) (π g)).symm

/-- Scalar compatibility with a homomorphism of the base rings, stated without choosing
new algebra instances on either crossed product. -/
theorem comapRingEquiv_algebraMap (e : K →+* R)
    (hι : ∀ k, ι (algebraMap K L k) = algebraMap R M (e k)) (k : K) :
    comapRingEquiv c ι π hπ (algebraMap R _ (e k)) = algebraMap K _ k := by
  rw [← (inc _).commutes, comapRingEquiv_inc, ← hι, ι.symm_apply_apply,
    (inc c).commutes]

section ScalarExtension

open TensorProduct

variable [Algebra K R]
  (hbase : Function.Bijective (algebraMap K R))
  (hι : ∀ k, ι (algebraMap K L k) = algebraMap R M (algebraMap K R k))

private def scalarExtensionRingEquiv : R ⊗[K] CrossedProduct c ≃+*
    CrossedProduct (c.comap (R := R) π ι hπ) :=
  (AlgEquiv.ofBijective (Algebra.TensorProduct.includeRight :
    CrossedProduct c →ₐ[K] R ⊗[K] CrossedProduct c)
    (Algebra.TensorProduct.includeRight_bijective hbase)).symm.toRingEquiv.trans
      (comapRingEquiv c ι π hπ).symm

private theorem scalarExtensionRingEquiv_includeRight (a : CrossedProduct c) :
    scalarExtensionRingEquiv c ι π hπ hbase (1 ⊗ₜ[K] a) =
      (comapRingEquiv c ι π hπ).symm a := by
  simp [scalarExtensionRingEquiv, ← Algebra.TensorProduct.includeRight_apply]

/-- Scalar extension along an isomorphism of base rings carries a crossed product to the
crossed product of the transported cocycle. This is the tensor-defined algebra transport. -/
def scalarExtensionEquiv : R ⊗[K] CrossedProduct c ≃ₐ[R]
    CrossedProduct (c.comap (R := R) π ι hπ) :=
  AlgEquiv.ofRingEquiv (f := scalarExtensionRingEquiv c ι π hπ hbase) (by
    intro r
    obtain ⟨k, rfl⟩ := hbase.surjective r
    apply (comapRingEquiv c ι π hπ).injective
    rw [← IsScalarTower.algebraMap_apply K R,
      ← (Algebra.TensorProduct.includeRight :
        CrossedProduct c →ₐ[K] R ⊗[K] CrossedProduct c).commutes]
    simp only [Algebra.TensorProduct.includeRight_apply,
      scalarExtensionRingEquiv_includeRight, RingEquiv.apply_symm_apply]
    exact (comapRingEquiv_algebraMap c ι π hπ (algebraMap K R) hι k).symm)

/-- A pure tensor maps to the transported element multiplied by its base scalar. -/
@[simp]
theorem scalarExtensionEquiv_tmul (r : R) (a : CrossedProduct c) :
    scalarExtensionEquiv c ι π hπ hbase hι (r ⊗ₜ[K] a) =
      r • (comapRingEquiv c ι π hπ).symm a := by
  calc
    _ = scalarExtensionEquiv c ι π hπ hbase hι (r • (1 ⊗ₜ[K] a)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = r • scalarExtensionEquiv c ι π hπ hbase hι (1 ⊗ₜ[K] a) := map_smul _ _ _
    _ = _ := congrArg (r • ·) (scalarExtensionRingEquiv_includeRight c ι π hπ hbase a)

/-- The inverse scalar-extension transport is the unit tensor of the ring transport. -/
@[simp]
theorem scalarExtensionEquiv_symm_apply (a : CrossedProduct (c.comap (R := R) π ι hπ)) :
    (scalarExtensionEquiv c ι π hπ hbase hι).symm a =
      1 ⊗ₜ[K] comapRingEquiv c ι π hπ a := by
  apply (scalarExtensionEquiv c ι π hπ hbase hι).injective
  simp

end ScalarExtension

end TauCeti.CrossedProduct
