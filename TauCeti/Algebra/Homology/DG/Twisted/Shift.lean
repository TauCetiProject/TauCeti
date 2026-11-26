/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import TauCeti.Algebra.Homology.DG.Module.Right.Shift
public import TauCeti.Algebra.Homology.DG.Twisted.Complex

/-!
# Twisted complexes of shifted coefficients

Let `m` be a twisting cocycle on a finite set `P` of generators graded by `ind`, with values in a
differential graded algebra `A`, and let `M` be a DG right module over `A`. This file compares the
twisted complex `M ⊗ ⟨P⟩` (`TauCeti.TwistingCocycle.twistedCochainComplex`) of a shifted module
with the shifted twisted complex.

* The twisted complex is functorial in the coefficient module: a morphism `f : M ⟶ N` acts on
  `M ⊗ ⟨P⟩ = P → M` coefficientwise (`TauCeti.TwistingCocycle.twistedCochainComplexMap`,
  `TauCeti.TwistingCocycle.twistedCochainComplexFunctor`).
* **The shift.** For the shift `M[n]` of `TauCeti.DGRightModuleCat.shift`, with `M[n]ᵖ = Mᵖ⁺ⁿ`,
  differential `(-1)^n dM` and unchanged action, an element `α ⊗ x` of `M ⊗ ⟨P⟩` of total degree
  `k + n` has total degree `k` in `M[n] ⊗ ⟨P⟩`, and the twisted differential of `M[n]` is `(-1)^n`
  times that of `M` (`TauCeti.shiftPiEquiv_twistedDifferential`): the sign of `dM`
  is that of the shift, and the Koszul sign `(-1)^|α|` of the twisted term changes by `(-1)^n`
  with the degree. These are the degrees and the differential of the shift `(M ⊗ ⟨P⟩)[n]` of
  cochain complexes, so the identity of `P → M` is an isomorphism `M[n] ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]`
  (`TauCeti.TwistingCocycle.twistedCochainComplexShiftIso`), natural in `M`
  (`TauCeti.TwistingCocycle.twistedCochainComplexShiftNatIso`).
* **The right shift.** For the right shift `M ⊗ R[n]` of `TauCeti.DGRightModuleCat.rightShift`,
  with the unsigned differential and an element of `A` of degree `e` acting by `(-1)^(n e)` times
  its action on `M`, the identity of `P → M` is not in general a chain map to `(M ⊗ ⟨P⟩)[n]`:
  against the differential of the shifted complex, the term `dM α` of the twisted differential is
  off by the sign `(-1)^n` and the term `α · m x y` by `(-1)^(n e)`, with
  `e = ind y - ind x + 1`. The isomorphism
  `(M ⊗ R[n]) ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]` (`TauCeti.TwistingCocycle.twistedCochainComplexRightShiftIso`)
  multiplies the coefficient `α` of each generator by the Koszul factor `(-1)^(n p)`, where `p` is
  the degree of `α` in `M`
  (`TauCeti.TwistingCocycle.twistedCochainComplexRightShiftIso_hom_f_apply`). It is the image of
  the exchange of suspensions `M ⊗ R[n] ≅ M[n]` (`TauCeti.DGRightModuleCat.rightShiftIsoShift`)
  under the functoriality, followed by the shift isomorphism, and it is natural in `M`
  (`TauCeti.TwistingCocycle.twistedCochainComplexRightShiftNatIso`).

On cohomology both give `Hᵏ(M[n] ⊗ ⟨P⟩) ≅ Hᵏ⁺ⁿ(M ⊗ ⟨P⟩)`
(`TauCeti.TwistingCocycle.twistedHomologyShiftIso`,
`TauCeti.TwistingCocycle.twistedHomologyRightShiftIso`).

The right shift is the shape of the tensor product `𝓕 ⊗ L[n]` of a DG local system with a
rank-one local system whose generator sits in homological degree `-n`: in the cohomological
grading of DG local systems, `TauCeti.RankOneLocalSystem.shiftedTensor` is `𝓕 ↦ (𝓕 ⊗ L) ⊗ R[-n]`.
So `twistedCochainComplexRightShiftIso` with shift `-n` identifies the twisted complex with
coefficients in `𝓕 ⊗ L[n]` with the twisted complex with coefficients in `𝓕 ⊗ L`, shifted by `n`
in the homological grading, through the Koszul factor `(-1)^(n p)` on a coefficient of homological
degree `p`. In the Viterbo isomorphism of Barraud, Damian, Humilière and Oancea the graded twist
is `η_gr = η₀[n]`, and this is the comparison of the twisted complexes with coefficients in
`𝓕 ⊗ η_gr` and in `𝓕 ⊗ η₀`, through the same map as the comparison of the coefficients
(`TauCeti.RankOneLocalSystem.shiftedTensorIsoShift`).

## Main definitions

* `TauCeti.TwistingCocycle.twistedCochainComplexMap`: the map of twisted complexes induced by a
  morphism of coefficient modules, and `TauCeti.TwistingCocycle.twistedCochainComplexFunctor`,
  the twisted complex as a functor of the coefficient module.
* `TauCeti.TwistingCocycle.twistedCochainComplexShiftIso`: `M[n] ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]`.
* `TauCeti.TwistingCocycle.twistedCochainComplexRightShiftIso`:
  `(M ⊗ R[n]) ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]`.
* `TauCeti.TwistingCocycle.twistedHomologyShiftIso`,
  `TauCeti.TwistingCocycle.twistedHomologyRightShiftIso`: the isomorphisms on cohomology.

## Main results

* `TauCeti.TwistingCocycle.twistedCochainComplexXEquiv_twistedCochainComplexShiftIso_hom_f_apply`:
  the shift isomorphism is the identity of `P → M`.
* `TauCeti.TwistingCocycle.twistedCochainComplexRightShiftIso_hom_f_apply`: the right-shift
  isomorphism multiplies each coefficient of degree `p` by `(-1)^(n p)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4, 1.5 and 4.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P : Type uP} {ind : P → ℤ}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

/-! ### Coefficientwise maps and the shift on `P → M` -/

section Coefficients

variable {M N : DGRightModuleCat.{uR, uA, uM} h}

/-- A morphism of coefficient modules, applied coefficientwise, preserves the total degree. -/
theorem comp_mem_twistedTotalGrading (f : M ⟶ N) {k : ℤ} {g : P → M}
    (hg : g ∈ twistedTotalGrading M.grading ind k) :
    (fun x ↦ f (g x)) ∈ twistedTotalGrading N.grading ind k :=
  mem_twistedTotalGrading_iff.2 fun x ↦ f.map_mem' (mem_twistedTotalGrading_iff.1 hg x)

/-- A morphism of coefficient modules, applied coefficientwise, commutes with the twisted
differentials of any matrix. -/
theorem twistedDifferential_comp [Fintype P] (m : P → P → A) (f : M ⟶ N) (g : P → M) :
    twistedDifferential m N.grading N.differential (fun x ↦ f (g x)) =
      fun y ↦ f (twistedDifferential m M.grading M.differential g y) := by
  funext y
  simp only [twistedDifferential_apply, map_add, map_sum, DGRightModuleCat.map_d]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← DGRightModuleHom.map_koszulTwist f, map_smul]

variable (M) (n : ℤ)

/-- The identification of `P → M[n]` with `P → M`, the identity of the underlying elements. -/
noncomputable def DGRightModuleCat.shiftPiEquiv : (P → M.shift n) ≃ₗ[R] (P → M) :=
  LinearEquiv.piCongrRight fun _ ↦ (M.shiftEquiv n).restrictScalars R

@[simp]
theorem DGRightModuleCat.shiftPiEquiv_apply (g : P → M.shift n) (x : P) :
    M.shiftPiEquiv n g x = M.shiftEquiv n (g x) :=
  (rfl)

@[simp]
theorem DGRightModuleCat.shiftPiEquiv_symm_apply (g : P → M) (x : P) :
    (M.shiftPiEquiv n).symm g x = (M.shiftEquiv n).symm (g x) :=
  (rfl)

/-- An element of `P → M` has total degree `k` in `M[n] ⊗ ⟨P⟩` exactly when it has total degree
`k + n` in `M ⊗ ⟨P⟩`. -/
theorem map_twistedTotalGrading_shiftPiEquiv (k : ℤ) :
    (twistedTotalGrading (M.shift n).grading ind k).map (M.shiftPiEquiv (P := P) n).toLinearMap =
      twistedTotalGrading M.grading ind (k + n) := by
  ext g
  rw [Submodule.mem_map_equiv, mem_twistedTotalGrading_iff, mem_twistedTotalGrading_iff]
  refine forall_congr' fun x ↦ ?_
  rw [← M.shiftEquiv_mem_grading_iff n, add_right_comm, DGRightModuleCat.shiftPiEquiv_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- **The twisted differential of `M[n]` is `(-1)^n` times that of `M`**, for any matrix: the
differential of `M[n]` is `(-1)^n dM`, and the Koszul sign of an element of `M[n]` differs from its
sign in `M` by `(-1)^n`. -/
theorem shiftPiEquiv_twistedDifferential [Fintype P] (m : P → P → A) (g : P → M.shift n) :
    M.shiftPiEquiv n (twistedDifferential m (M.shift n).grading (M.shift n).differential g) =
      n.negOnePow • twistedDifferential m M.grading M.differential (M.shiftPiEquiv n g) := by
  funext y
  simp only [DGRightModuleCat.shiftPiEquiv_apply, twistedDifferential_apply, map_add, map_sum,
    M.shiftEquiv_differential, Pi.smul_apply, smul_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [LinearEquiv.map_smul, M.shiftEquiv_koszulTwist, one_mul, smul_comm]

end Coefficients

namespace TwistingCocycle

variable [Fintype P] (m : TwistingCocycle 𝒜 d P ind)

/-! ### Functoriality in the coefficient module -/

section Map

variable {M N Q : DGRightModuleCat.{uR, uA, uM} h}

/-- The degree-`k` component of the map of twisted complexes induced by `f`. -/
private noncomputable def twistedCochainComplexMapX (f : M ⟶ N) (k : ℤ) :
    (m.twistedCochainComplex M.differential M.isDGRightModule).X k ⟶
      (m.twistedCochainComplex N.differential N.isDGRightModule).X k :=
  ModuleCat.ofHom <|
    (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k).symm.toLinearMap ∘ₗ
      ((LinearMap.compLeft (f.toLinearMap.restrictScalars R) P).restrict
        fun _ hg ↦ comp_mem_twistedTotalGrading f hg) ∘ₗ
      (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule k).toLinearMap

private theorem twistedCochainComplexXEquiv_twistedCochainComplexMapX (f : M ⟶ N) (k : ℤ)
    (g : (m.twistedCochainComplex M.differential M.isDGRightModule).X k) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k
        ((m.twistedCochainComplexMapX f k).hom g) : P → N) =
      fun x ↦ f ((twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule k g :
        P → M) x) := by
  simp only [twistedCochainComplexMapX, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  -- The restriction of `LinearMap.compLeft` applies `f` to each coefficient.
  rfl

/-- **The map of twisted complexes induced by a morphism of coefficient modules** `f : M ⟶ N`:
on `M ⊗ ⟨P⟩ = P → M` it applies `f` to the coefficient of each generator. -/
noncomputable def twistedCochainComplexMap (f : M ⟶ N) :
    m.twistedCochainComplex M.differential M.isDGRightModule ⟶
      m.twistedCochainComplex N.differential N.isDGRightModule where
  f k := m.twistedCochainComplexMapX f k
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext g
    apply (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule (i + 1)).injective
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [twistedCochainComplexXEquiv_twistedCochainComplexMapX, twistedCochainComplexXEquiv_d,
      twistedCochainComplexXEquiv_d, twistedCochainComplexXEquiv_twistedCochainComplexMapX,
      twistedDifferential_comp m.m]

/-- The map induced by `f` applies `f` to the coefficient of each generator. -/
@[simp]
theorem twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply (f : M ⟶ N) (k : ℤ)
    (g : (m.twistedCochainComplex M.differential M.isDGRightModule).X k) (x : P) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k
        (((m.twistedCochainComplexMap f).f k).hom g) : P → N) x =
      f ((twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule k g : P → M) x) :=
  congrFun (m.twistedCochainComplexXEquiv_twistedCochainComplexMapX f k g) x

/-- Two maps of twisted complexes agree when they agree on the coefficients of every
generator. -/
theorem twistedCochainComplex_hom_ext
    {φ ψ : m.twistedCochainComplex M.differential M.isDGRightModule ⟶
      m.twistedCochainComplex N.differential N.isDGRightModule}
    (H : ∀ k g x,
      (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k
          ((φ.f k).hom g) : P → N) x =
        (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k
          ((ψ.f k).hom g) : P → N) x) : φ = ψ := by
  ext k g
  exact (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k).injective
    (Subtype.ext (funext (H k g)))

/-- The identity of the coefficient module induces the identity of the twisted complex. -/
@[simp]
theorem twistedCochainComplexMap_id :
    m.twistedCochainComplexMap (𝟙 M) = 𝟙 _ :=
  m.twistedCochainComplex_hom_ext fun k g x ↦ by
    rw [twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      DGRightModuleCat.id_apply, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

/-- The map induced by a composite is the composite of the induced maps. -/
@[simp]
theorem twistedCochainComplexMap_comp (f : M ⟶ N) (g : N ⟶ Q) :
    m.twistedCochainComplexMap (f ≫ g) =
      m.twistedCochainComplexMap f ≫ m.twistedCochainComplexMap g :=
  m.twistedCochainComplex_hom_ext fun k c x ↦ by
    rw [twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      DGRightModuleCat.comp_apply, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply]

variable (h) in
/-- **The twisted complex as a functor of the coefficient module**: `M ↦ M ⊗ ⟨P⟩`. Its body is
exposed so that its objects are the twisted complexes. -/
@[expose] noncomputable def twistedCochainComplexFunctor :
    DGRightModuleCat.{uR, uA, uM} h ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ where
  obj M := m.twistedCochainComplex M.differential M.isDGRightModule
  map f := m.twistedCochainComplexMap f

@[simp]
theorem twistedCochainComplexFunctor_obj (M : DGRightModuleCat.{uR, uA, uM} h) :
    (m.twistedCochainComplexFunctor h).obj M =
      m.twistedCochainComplex M.differential M.isDGRightModule :=
  (rfl)

@[simp]
theorem twistedCochainComplexFunctor_map (f : M ⟶ N) :
    (m.twistedCochainComplexFunctor h).map f = m.twistedCochainComplexMap f :=
  (rfl)

/-- The isomorphism of twisted complexes induced by an isomorphism of coefficient modules, the image
of `e` under `twistedCochainComplexFunctor`, between the twisted complexes themselves. -/
noncomputable def twistedCochainComplexMapIso (e : M ≅ N) :
    m.twistedCochainComplex M.differential M.isDGRightModule ≅
      m.twistedCochainComplex N.differential N.isDGRightModule :=
  (m.twistedCochainComplexFunctor h).mapIso e

@[simp]
theorem twistedCochainComplexMapIso_hom (e : M ≅ N) :
    (m.twistedCochainComplexMapIso e).hom = m.twistedCochainComplexMap e.hom :=
  (rfl)

@[simp]
theorem twistedCochainComplexMapIso_inv (e : M ≅ N) :
    (m.twistedCochainComplexMapIso e).inv = m.twistedCochainComplexMap e.inv :=
  (rfl)

end Map

/-- Under `twistedCochainComplexXEquiv`, the differential of the twisted complex between any two
consecutive degrees is the twisted differential. -/
private theorem twistedCochainComplexXEquiv_d_of_add_one_eq (M : DGRightModuleCat.{uR, uA, uM} h)
    {p q : ℤ} (hpq : p + 1 = q)
    (g : (m.twistedCochainComplex M.differential M.isDGRightModule).X p) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule q
        (((m.twistedCochainComplex M.differential M.isDGRightModule).d p q).hom g) : P → M) =
      twistedDifferential m.m M.grading M.differential
        (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule p g) := by
  subst hpq
  exact twistedCochainComplexXEquiv_d m.mem_graded m.twisting M.isDGRightModule p g

/-! ### The shift `M[n]` -/

section Shift

variable (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ)

/-- The degree-`k` part of the isomorphism `M[n] ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]`. -/
private noncomputable def twistedCochainComplexShiftXEquiv (k : ℤ) :
    (m.twistedCochainComplex (M.shift n).differential (M.shift n).isDGRightModule).X k ≃ₗ[R]
      ((m.twistedCochainComplex M.differential M.isDGRightModule)⟦n⟧).X k :=
  (twistedCochainComplexXEquiv m.mem_graded m.twisting (M.shift n).isDGRightModule k).trans <|
    ((M.shiftPiEquiv n).ofSubmodules _ _ (map_twistedTotalGrading_shiftPiEquiv M n k)).trans
      (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule (k + n)).symm

/-- The degree-`k` part of the shift isomorphism is the identity of the underlying elements. -/
private theorem twistedCochainComplexXEquiv_twistedCochainComplexShiftXEquiv (k : ℤ)
    (g : (m.twistedCochainComplex (M.shift n).differential (M.shift n).isDGRightModule).X k) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule (k + n)
        (m.twistedCochainComplexShiftXEquiv M n k g) : P → M) =
      M.shiftPiEquiv n
        (twistedCochainComplexXEquiv m.mem_graded m.twisting (M.shift n).isDGRightModule k g) := by
  simp [twistedCochainComplexShiftXEquiv]

/-- **The twisted complex of a shifted module is the shifted twisted complex**:
`M[n] ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]`, through the identity of `P → M`. -/
noncomputable def twistedCochainComplexShiftIso :
    m.twistedCochainComplex (M.shift n).differential (M.shift n).isDGRightModule ≅
      (m.twistedCochainComplex M.differential M.isDGRightModule)⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (m.twistedCochainComplexShiftXEquiv M n k).toModuleIso) fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      ext g
      apply (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule
        (i + 1 + n)).injective
      apply Subtype.ext
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe, CochainComplex.shiftFunctor_obj_d',
        Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]
      rw [map_zsmul, Submodule.coe_smul_of_tower,
        m.twistedCochainComplexXEquiv_d_of_add_one_eq M (by ring),
        twistedCochainComplexXEquiv_twistedCochainComplexShiftXEquiv,
        twistedCochainComplexXEquiv_twistedCochainComplexShiftXEquiv,
        twistedCochainComplexXEquiv_d, shiftPiEquiv_twistedDifferential, Units.smul_def]

/-- The shift isomorphism is the identity of the underlying elements of `P → M`. -/
theorem twistedCochainComplexXEquiv_twistedCochainComplexShiftIso_hom_f_apply (k : ℤ)
    (g : (m.twistedCochainComplex (M.shift n).differential (M.shift n).isDGRightModule).X k) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule (k + n)
        (((m.twistedCochainComplexShiftIso M n).hom.f k).hom g) : P → M) =
      M.shiftPiEquiv n
        (twistedCochainComplexXEquiv m.mem_graded m.twisting (M.shift n).isDGRightModule k g) :=
  m.twistedCochainComplexXEquiv_twistedCochainComplexShiftXEquiv M n k g

/-- The inverse of the shift isomorphism is again the identity of the underlying elements. -/
theorem twistedCochainComplexXEquiv_twistedCochainComplexShiftIso_inv_f_apply (k : ℤ)
    (g : ((m.twistedCochainComplex M.differential M.isDGRightModule)⟦n⟧).X k) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting (M.shift n).isDGRightModule k
        (((m.twistedCochainComplexShiftIso M n).inv.f k).hom g) : P → M.shift n) =
      (M.shiftPiEquiv n).symm
        (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule (k + n) g) := by
  rw [LinearEquiv.eq_symm_apply,
    ← twistedCochainComplexXEquiv_twistedCochainComplexShiftIso_hom_f_apply, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]

variable (h) in
/-- The isomorphisms `M[n] ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]` are natural in `M`. -/
noncomputable def twistedCochainComplexShiftNatIso :
    DGRightModuleCat.shiftFunctor n ⋙ m.twistedCochainComplexFunctor h ≅
      m.twistedCochainComplexFunctor h ⋙ CategoryTheory.shiftFunctor _ n :=
  NatIso.ofComponents (fun M ↦ m.twistedCochainComplexShiftIso M n) fun {M N} f ↦ by
    -- Unfold the functors, so that their objects are the twisted complexes themselves.
    dsimp only [Functor.comp_obj, Functor.comp_map, twistedCochainComplexFunctor]
    ext k g
    apply (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule (k + n)).injective
    apply Subtype.ext
    funext x
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctor_map_f']
    rw [twistedCochainComplexXEquiv_twistedCochainComplexShiftIso_hom_f_apply,
      DGRightModuleCat.shiftPiEquiv_apply,
      twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      twistedCochainComplexXEquiv_twistedCochainComplexShiftIso_hom_f_apply,
      DGRightModuleCat.shiftPiEquiv_apply, DGRightModuleCat.shiftEquiv_shiftFunctor_map]

/-- The component of `twistedCochainComplexShiftNatIso` at `M` is
`twistedCochainComplexShiftIso`. -/
@[simp]
theorem twistedCochainComplexShiftNatIso_app :
    (m.twistedCochainComplexShiftNatIso h n).app M = m.twistedCochainComplexShiftIso M n :=
  (rfl)

/-- On cohomology, `Hᵏ(M[n] ⊗ ⟨P⟩) ≅ Hᵏ⁺ⁿ(M ⊗ ⟨P⟩)`. -/
noncomputable def twistedHomologyShiftIso (k k' : ℤ) (hk : n + k = k') :
    (m.twistedCochainComplex (M.shift n).differential (M.shift n).isDGRightModule).homology k ≅
      (m.twistedCochainComplex M.differential M.isDGRightModule).homology k' :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (m.twistedCochainComplexShiftIso M n) ≪≫
    (CochainComplex.ShiftSequence.shiftIso _ n k k' hk).app _

end Shift

/-! ### The right shift `M ⊗ R[n]` -/

section RightShift

variable (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ)

/-- **The twisted complex of a right-shifted module is the shifted twisted complex**:
`(M ⊗ R[n]) ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]`, multiplying the coefficient of each generator by the Koszul
sign of exchanging the two suspensions (`twistedCochainComplexRightShiftIso_hom_f_apply`). -/
noncomputable def twistedCochainComplexRightShiftIso :
    m.twistedCochainComplex (M.rightShift n).differential (M.rightShift n).isDGRightModule ≅
      (m.twistedCochainComplex M.differential M.isDGRightModule)⟦n⟧ :=
  m.twistedCochainComplexMapIso (M.rightShiftIsoShift n) ≪≫ m.twistedCochainComplexShiftIso M n

/-- **The Koszul factor of the right-shift isomorphism**: it multiplies the coefficient `α` of each
generator by `(-1)^(n p)` on the part of degree `p` of `α` in `M`, the Koszul twist of
parameter `n`. -/
theorem twistedCochainComplexRightShiftIso_hom_f_apply (k : ℤ)
    (g : (m.twistedCochainComplex (M.rightShift n).differential
      (M.rightShift n).isDGRightModule).X k) (x : P) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule (k + n)
        (((m.twistedCochainComplexRightShiftIso M n).hom.f k).hom g) : P → M) x =
      (InternalGrading.ofDecomposition M.grading).koszulTwist n
        (M.rightShiftEquiv n ((twistedCochainComplexXEquiv m.mem_graded m.twisting
          (M.rightShift n).isDGRightModule k g : P → M.rightShift n) x)) := by
  simp only [twistedCochainComplexRightShiftIso, Iso.trans_hom, twistedCochainComplexMapIso_hom,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [twistedCochainComplexXEquiv_twistedCochainComplexShiftIso_hom_f_apply,
      DGRightModuleCat.shiftPiEquiv_apply,
    twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
    DGRightModuleCat.shiftEquiv_rightShiftIsoShift_hom_apply]

variable (h) in
/-- The isomorphisms `(M ⊗ R[n]) ⊗ ⟨P⟩ ≅ (M ⊗ ⟨P⟩)[n]` are natural in `M`. -/
noncomputable def twistedCochainComplexRightShiftNatIso :
    DGRightModuleCat.rightShiftFunctor n ⋙ m.twistedCochainComplexFunctor h ≅
      m.twistedCochainComplexFunctor h ⋙ CategoryTheory.shiftFunctor _ n :=
  NatIso.ofComponents (fun M ↦ m.twistedCochainComplexRightShiftIso M n) fun {M N} f ↦ by
    -- Unfold the functors, so that their objects are the twisted complexes themselves.
    dsimp only [Functor.comp_obj, Functor.comp_map, twistedCochainComplexFunctor]
    ext k g
    apply (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule (k + n)).injective
    apply Subtype.ext
    funext x
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctor_map_f']
    rw [twistedCochainComplexRightShiftIso_hom_f_apply,
      twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      twistedCochainComplexRightShiftIso_hom_f_apply,
      DGRightModuleCat.rightShiftEquiv_rightShiftFunctor_map, DGRightModuleHom.map_koszulTwist]

/-- The component of `twistedCochainComplexRightShiftNatIso` at `M` is
`twistedCochainComplexRightShiftIso`. -/
@[simp]
theorem twistedCochainComplexRightShiftNatIso_app :
    (m.twistedCochainComplexRightShiftNatIso h n).app M =
      m.twistedCochainComplexRightShiftIso M n :=
  (rfl)

/-- On cohomology, `Hᵏ((M ⊗ R[n]) ⊗ ⟨P⟩) ≅ Hᵏ⁺ⁿ(M ⊗ ⟨P⟩)`. -/
noncomputable def twistedHomologyRightShiftIso (k k' : ℤ) (hk : n + k = k') :
    (m.twistedCochainComplex (M.rightShift n).differential
        (M.rightShift n).isDGRightModule).homology k ≅
      (m.twistedCochainComplex M.differential M.isDGRightModule).homology k' :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (m.twistedCochainComplexRightShiftIso M n) ≪≫
    (CochainComplex.ShiftSequence.shiftIso _ n k k' hk).app _

end RightShift

end TwistingCocycle

end TauCeti
