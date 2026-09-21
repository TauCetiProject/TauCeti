/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.NormalBasis
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup

/-!
# Normal bases as representations

Let `L/K` be a finite Galois extension with Galois group `Gal(L/K)`. The normal basis theorem
identifies the additive representation on `L` with the representation induced from the trivial
subgroup, and over `K` with the left regular representation.

## Main definitions

* `TauCeti.galoisAddRep`: the additive representation of `Gal(L/K)` on `L`.
* `TauCeti.normalBasisFinsuppEquiv`: normal-basis coordinates, indexed compatibly with induction.
* `TauCeti.galoisAddRepIsoIndBot`: the additive representation is induced from the trivial
  subgroup.
* `TauCeti.galoisAddRepIsoLeftRegular`: over `K`, it is the left regular representation.
-/

public noncomputable section

open CategoryTheory Rep

namespace TauCeti

universe u

variable (R K L : Type u) [CommRing R] [Field K] [Field L] [Algebra K L]
  [Algebra R K] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- The `R`-linear representation of `Gal(L/K)` on the additive group of `L`, where `R` acts on
`L` through `K`. Mathlib's `Rep.ofAlgebraAut K L` is the case `R = ℤ`; the case `R = K` is the one
in which a normal basis is available. -/
abbrev galoisAddRep : Rep R Gal(L/K) := Rep.ofDistribMulAction R Gal(L/K) L

/-- The Galois group permutes a normal basis by left translation. -/
theorem smul_normalBasis (σ i : Gal(L/K)) :
    σ • IsGalois.normalBasis K L i = IsGalois.normalBasis K L (σ * i) := by
  rw [IsGalois.normalBasis_apply i, IsGalois.normalBasis_apply (σ * i), AlgEquiv.smul_def,
    AlgEquiv.mul_apply]

/-- Acting by `σ` translates the coordinates of a normal basis by `σ`. -/
theorem repr_normalBasis_smul (σ : Gal(L/K)) (x : L) (e : Gal(L/K)) :
    (IsGalois.normalBasis K L).repr (σ • x) e =
      (IsGalois.normalBasis K L).repr x (σ⁻¹ * e) := by
  classical
  set b := IsGalois.normalBasis K L
  have key : Finsupp.lapply e ∘ₗ b.repr.toLinearMap ∘ₗ σ.toLinearMap =
      Finsupp.lapply (σ⁻¹ * e) ∘ₗ b.repr.toLinearMap :=
    b.ext fun i ↦ by
      have hi : σ.toLinearMap (b i) = b (σ * i) := smul_normalBasis K L σ i
      simp only [LinearMap.comp_apply, hi, LinearEquiv.coe_coe, Module.Basis.repr_self,
        Finsupp.lapply_apply, Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  simpa only [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply, AlgEquiv.smul_def] using LinearMap.congr_fun key x

/-- Coordinates in a normal basis, read backwards along inversion of the Galois group: an
`R`-linear identification of `L` with the finitely supported functions from `Gal(L/K)` to `K`.
Inverting the index turns the left translation of `smul_normalBasis` into the right translation
by which `Rep.indBot` acts. -/
def normalBasisFinsuppEquiv : L ≃ₗ[R] (Gal(L/K) →₀ K) :=
  ((IsGalois.normalBasis K L).repr.restrictScalars R).trans
    (Finsupp.domLCongr (Equiv.inv Gal(L/K)))

@[simp]
theorem normalBasisFinsuppEquiv_apply (x : L) (γ : Gal(L/K)) :
    normalBasisFinsuppEquiv R K L x γ = (IsGalois.normalBasis K L).repr x γ⁻¹ := by
  simp [normalBasisFinsuppEquiv]

theorem normalBasisFinsuppEquiv_smul (σ : Gal(L/K)) (x : L) (γ : Gal(L/K)) :
    normalBasisFinsuppEquiv R K L (σ • x) γ = normalBasisFinsuppEquiv R K L x (γ * σ) := by
  rw [normalBasisFinsuppEquiv_apply, normalBasisFinsuppEquiv_apply, repr_normalBasis_smul,
    mul_inv_rev]

/-- The additive group of `L`, transported by a normal basis to the module underlying the
representation induced from the trivial subgroup. -/
def galoisAddRepEquivIndBot : L ≃ₗ[R] (Rep.indBot R Gal(L/K) K : Type u) :=
  (normalBasisFinsuppEquiv R K L).trans (Rep.indBotEquivFinsupp R Gal(L/K) K).symm

@[simp]
theorem indBotEquivFinsupp_galoisAddRepEquivIndBot (x : L) :
    Rep.indBotEquivFinsupp R Gal(L/K) K (galoisAddRepEquivIndBot R K L x) =
      normalBasisFinsuppEquiv R K L x := by
  simp [galoisAddRepEquivIndBot]

theorem galoisAddRepEquivIndBot_smul (σ : Gal(L/K)) (x : L) :
    galoisAddRepEquivIndBot R K L (σ • x) =
      (Rep.indBot R Gal(L/K) K).ρ σ (galoisAddRepEquivIndBot R K L x) := by
  refine (Rep.indBotEquivFinsupp R Gal(L/K) K).injective (Finsupp.ext fun γ ↦ ?_)
  rw [Rep.indBotEquivFinsupp_ρ_apply, indBotEquivFinsupp_galoisAddRepEquivIndBot,
    indBotEquivFinsupp_galoisAddRepEquivIndBot]
  exact normalBasisFinsuppEquiv_smul R K L σ x γ

/-- **The additive group of a finite Galois extension is induced from the trivial subgroup**: a
normal basis exhibits `L` as `Ind_1^{Gal(L/K)} K`, equivalently as a free `K[Gal(L/K)]`-module of
rank one. -/
def galoisAddRepIsoIndBot : galoisAddRep R K L ≅ Rep.indBot R Gal(L/K) K :=
  Rep.mkIso <| Representation.Equiv.mk (galoisAddRepEquivIndBot R K L) fun σ ↦
    LinearMap.ext fun x ↦ galoisAddRepEquivIndBot_smul R K L σ x

@[simp]
theorem galoisAddRepIsoIndBot_hom_apply (x : L) :
    (galoisAddRepIsoIndBot R K L).hom.hom x = galoisAddRepEquivIndBot R K L x :=
  (rfl)

/-- **Normal basis theorem, representation form**: over the base field, the additive group of `L`
is the left regular representation `K[Gal(L/K)]`. -/
def galoisAddRepIsoLeftRegular : galoisAddRep K K L ≅ Rep.leftRegular K Gal(L/K) :=
  galoisAddRepIsoIndBot K K L ≪≫ Rep.indBotIsoLeftRegular

/-- The coefficient of a group element under the normal-basis representation isomorphism is its
normal-basis coordinate. -/
@[simp]
theorem galoisAddRepIsoLeftRegular_hom_hom_apply_coeff (x : L) (σ : Gal(L/K)) :
    ((galoisAddRepIsoLeftRegular K L).hom.hom x).coeff σ =
      (IsGalois.normalBasis K L).repr x σ := by
  change ((Rep.indBotIsoLeftRegular.hom.hom
    ((galoisAddRepIsoIndBot K K L).hom.hom x))).coeff σ = _
  rw [Rep.indBotIsoLeftRegular_hom_hom_apply_coeff, galoisAddRepIsoIndBot_hom_apply,
    indBotEquivFinsupp_galoisAddRepEquivIndBot, normalBasisFinsuppEquiv_apply]
  simp

/-- The inverse normal-basis representation isomorphism sends a group-algebra basis element to
the corresponding normal-basis vector. -/
@[simp]
theorem galoisAddRepIsoLeftRegular_inv_hom_single (σ : Gal(L/K)) (r : K) :
    (galoisAddRepIsoLeftRegular K L).inv.hom (MonoidAlgebra.single σ r) =
      r • IsGalois.normalBasis K L σ := by
  have h : (galoisAddRepIsoLeftRegular K L).hom.hom
      (r • IsGalois.normalBasis K L σ) = MonoidAlgebra.single σ r := by
    ext γ
    rw [galoisAddRepIsoLeftRegular_hom_hom_apply_coeff]
    simp
  rw [← h]
  exact Rep.inv_hom_apply _ _ (galoisAddRepIsoLeftRegular K L)
    (r • IsGalois.normalBasis K L σ)

end TauCeti
