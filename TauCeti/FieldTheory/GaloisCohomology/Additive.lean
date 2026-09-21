/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced

/-!
# The additive group of a finite Galois extension is cohomologically trivial

Let `L/K` be a finite Galois extension with Galois group `Γ = Gal(L/K)`. The normal basis theorem
`IsGalois.normalBasis` produces a `K`-basis of `L` indexed by `Γ` on which `Γ` acts by left
translation, so `L` is free of rank one over the group algebra `K[Γ]`; equivalently, `L` is the
module induced from the trivial subgroup on `K`. Consequently every Tate cohomology group of `Γ`,
and of every subgroup of `Γ`, with coefficients in `L` vanishes: the additive group of `L` is a
cohomologically trivial `Γ`-module. This is the additive counterpart of Hilbert's theorem 90 and
the input that makes the units of an unramified extension of local fields cohomologically
trivial, through the filtration of the units by the additive graded pieces of the maximal ideal.

The coefficient ring is an arbitrary commutative ring `R` acting on `L` through `K`. The two cases
in use are `R = K`, where the statement is the classical one about `K`-vector spaces, and `R = ℤ`,
where the representation is Mathlib's `Rep.ofAlgebraAut K L` and the Tate groups are the abelian
groups that a class formation is built from.

## Main definitions

* `TauCeti.galoisAddRep`: the `R`-linear representation of `Gal(L/K)` on the additive group of
  `L`; for `R = ℤ` it is Mathlib's `Rep.ofAlgebraAut K L`.
* `TauCeti.normalBasisFinsuppEquiv`: the coordinates of a normal basis, as an identification of
  `L` with the finitely supported functions `Gal(L/K) →₀ K`.
* `TauCeti.galoisAddRepIsoIndBot`: `L` is induced from the trivial subgroup on `K`.
* `TauCeti.galoisAddRepIsoLeftRegular`: over the base field, `L` is the left regular
  representation `K[Gal(L/K)]`.

## Main results

* `TauCeti.isZero_tateCohomology_galoisAddRep` and
  `TauCeti.isZero_tateCohomology_res_galoisAddRep`: every Tate cohomology group of `Gal(L/K)`,
  and of any subgroup of it, with coefficients in `L` vanishes.
* `TauCeti.isZero_groupCohomology_galoisAddRep`: the additive form of Hilbert's theorem 90 and
  its higher analogues, `Hⁿ(Gal(L/K), L) = 0` for `n ≥ 1`.
* `TauCeti.mem_coinvariantsKer_of_trace_eq_zero`: the degree `-1` reading, that an element of
  trace zero is a sum of differences `σ y - y`.

## References

* J-P. Serre, *Local Fields*, Chapter X, §1, Proposition 1.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1 and Chapter III, §1.
-/

public noncomputable section

open CategoryTheory Limits Rep

namespace TauCeti

universe u

variable (R K L : Type u) [CommRing R] [Field K] [Field L] [Algebra K L]
  [Algebra R K] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- The `R`-linear representation of `Gal(L/K)` on the additive group of `L`, where `R` acts on
`L` through `K`. Mathlib's `Rep.ofAlgebraAut K L` is the case `R = ℤ`; the case `R = K` is the one
in which a normal basis is available. -/
abbrev galoisAddRep : Rep R Gal(L/K) := Rep.ofDistribMulAction R Gal(L/K) L

/-- The Galois group permutes a normal basis by left translation. -/
theorem normalBasis_smul (σ i : Gal(L/K)) :
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
      have hi : σ.toLinearMap (b i) = b (σ * i) := normalBasis_smul K L σ i
      simp only [LinearMap.comp_apply, hi, LinearEquiv.coe_coe, Module.Basis.repr_self,
        Finsupp.lapply_apply, Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  simpa only [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply, AlgEquiv.smul_def] using LinearMap.congr_fun key x

/-- Coordinates in a normal basis, read backwards along inversion of the Galois group: an
`R`-linear identification of `L` with the finitely supported functions from `Gal(L/K)` to `K`.
Inverting the index turns the left translation of `normalBasis_smul` into the right translation
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

/-- **The additive group of a finite Galois extension is cohomologically trivial**: every Tate
cohomology group of `Gal(L/K)` with coefficients in `L` vanishes. -/
theorem isZero_tateCohomology_galoisAddRep (r : ℤ) :
    IsZero (tateCohomology (galoisAddRep R K L) r) :=
  (TateCohomology.isZero_indBot K r).of_iso
    ((tateCohomologyFunctor r).mapIso (galoisAddRepIsoIndBot R K L))

/-- Every Tate cohomology group of a subgroup of `Gal(L/K)` with coefficients in `L` vanishes:
cohomological triviality is inherited by subgroups. -/
theorem isZero_tateCohomology_res_galoisAddRep (H : Subgroup Gal(L/K)) [Fintype H] (r : ℤ) :
    IsZero (tateCohomology (Rep.res H.subtype (galoisAddRep R K L)) r) :=
  (TateCohomology.isZero_res_indBot H K r).of_iso
    ((tateCohomologyFunctor r).mapIso ((Rep.resFunctor H.subtype).mapIso
      (galoisAddRepIsoIndBot R K L)))

/-- **Additive Hilbert 90 and its higher analogues**: the group cohomology of `Gal(L/K)` with
coefficients in `L` vanishes in every positive degree. -/
theorem isZero_groupCohomology_galoisAddRep (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (galoisAddRep R K L) n) :=
  (isZero_tateCohomology_galoisAddRep R K L n).of_iso
    ((_root_.TateCohomology.isoGroupCohomology n).app (galoisAddRep R K L)).symm

/-- The norm of the Galois representation on the additive group of `L` is the field trace. -/
theorem norm_ofDistribMulAction_eq_algebraMap_trace (x : L) :
    (Representation.ofDistribMulAction R Gal(L/K) L).norm x =
      algebraMap K L (Algebra.trace K L x) := by
  rw [Representation.norm_ofDistribMulAction_eq, _root_.trace_eq_sum_automorphisms]
  exact Finset.sum_congr rfl fun σ _ ↦ σ.smul_def x

/-- **Additive Hilbert 90 in degree `-1`**: an element of trace zero lies in the augmentation
submodule, that is, it is a sum of differences `σ y - y` with `σ` in the Galois group. -/
theorem mem_coinvariantsKer_of_trace_eq_zero {x : L} (hx : Algebra.trace K L x = 0) :
    x ∈ Representation.Coinvariants.ker (Representation.ofDistribMulAction R Gal(L/K) L) := by
  have hker : x ∈ LinearMap.ker (Representation.ofDistribMulAction R Gal(L/K) L).norm := by
    rw [LinearMap.mem_ker, norm_ofDistribMulAction_eq_algebraMap_trace, hx, map_zero]
  -- Degree `-1` Tate cohomology is the quotient of the norm kernel by the augmentation
  -- submodule, and it vanishes, so the two submodules agree.
  have : Subsingleton (tateCohomology (galoisAddRep R K L) (-1)) :=
    ModuleCat.subsingleton_of_isZero (isZero_tateCohomology_galoisAddRep R K L (-1))
  exact Submodule.mem_comap.1
    ((TateCohomology.HNegOneπ_eq_zero_iff (M := galoisAddRep R K L) ⟨x, hker⟩).1
      (Subsingleton.elim _ _))

end TauCeti
