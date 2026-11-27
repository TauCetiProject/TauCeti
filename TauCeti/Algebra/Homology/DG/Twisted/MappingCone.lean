/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Block
public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The twisted complex of the cone of a continuation cocycle is a mapping cone

Let `ν` be a continuation cocycle from a twisting cocycle `mP` on `(P, ind)` to a twisting cocycle
`mQ` on `(Q, indQ)`, without entries strictly increasing the index, and let
`ν.cone = [[mP, (-1) ^ ind x • ν], [0, mQ]]` be the block-triangular twisting cocycle on `P ⊕ Q`,
graded by `ind x + 1` on `P` and `indQ y` on `Q` (`TauCeti.ContinuationCocycle.cone`). For a
differential graded right module `(ℳ, dM)`, this file identifies the twisted complex `ℳ ⊗ ⟨P ⊕ Q⟩`
of `ν.cone` with the mapping cone (`CochainComplex.mappingCone`) of the continuation map
`Ψ : ℳ ⊗ ⟨P⟩ ⟶ ℳ ⊗ ⟨Q⟩` of `ν` (`TauCeti.ContinuationCocycle.continuationHom`)
(`TauCeti.ContinuationCocycle.coneTwistedCochainComplexIso`).

In total degree `n`, a family `f : P ⊕ Q → M` has `f (inl x)` of degree `n + 1 + ind x` and
`f (inr y)` of degree `n + indQ y`, so it is a pair of an element of degree `n + 1` of `ℳ ⊗ ⟨P⟩`
and an element of degree `n` of `ℳ ⊗ ⟨Q⟩`, as in the degree-`n` term of the mapping cone. The
twisted differential of the cone is block-triangular: on the `P`-part it is the twisted
differential `D_P` of `mP`, and its `Q`-part is `D_Q (f ∘ inr) + (-1) ^ (n + 1) • Ψ (f ∘ inl)`,
the Koszul sign of `f (inl x)` and the sign `(-1) ^ ind x` of the row combining to
`(-1) ^ (n + 1)` (`TauCeti.ContinuationCocycle.twistedDifferential_cone_apply_inl`,
`TauCeti.ContinuationCocycle.twistedDifferential_cone_apply_inr`, in
`TauCeti.Algebra.Homology.DG.Twisted.Block`). The mapping cone has differential
`(a, b) ↦ (-D_P a, Ψ a + D_Q b)`, so the identification multiplies the `P`-part in degree `n`
by `(-1) ^ (n + 1)` and keeps the `Q`-part.

Hence the continuation map of `ν` is a quasi-isomorphism exactly when the twisted complex of
`ν.cone` is acyclic (`TauCeti.ContinuationCocycle.quasiIso_continuationHom_iff_acyclic`). In the
same way, for a block-triangular twisting cocycle `m` on `P ⊕ Q`, which is the cone of its
off-diagonal block (`TauCeti.TwistingCocycle.cone_blockContinuation`), the continuation map of
that block is a quasi-isomorphism exactly when the twisted complex of `m` is acyclic
(`TauCeti.TwistingCocycle.quasiIso_blockContinuation_continuationHom_iff_acyclic`). This is the
form in which the twisting cocycle of a homotopy of Morse functions on a slab presents its
continuation map (see `TauCeti.Algebra.Homology.DG.Twisted.Block`): the continuation map is a
quasi-isomorphism exactly when the twisted complex of the slab is acyclic.

## Main definitions

* `TauCeti.ContinuationCocycle.coneTwistedCochainComplexIso`: the isomorphism between the twisted
  complex of `ν.cone` and the mapping cone of the continuation map of `ν`.

## Main results

* `ContinuationCocycle.twistedCochainComplexXEquiv_fst_v_coneTwistedCochainComplexIso_hom_f_apply`,
  `ContinuationCocycle.twistedCochainComplexXEquiv_snd_v_coneTwistedCochainComplexIso_hom_f_apply`:
  the two components of the isomorphism, `f ↦ ((-1) ^ (n + 1) • f ∘ inl, f ∘ inr)` in degree `n`.
* `ContinuationCocycle.twistedCochainComplexXEquiv_coneTwistedCochainComplexIso_inv_f_inl_v_apply`,
  `ContinuationCocycle.twistedCochainComplexXEquiv_coneTwistedCochainComplexIso_inv_f_inr_f_apply`:
  its inverse on the two summands of the mapping cone, extension by zero with the same signs.
* `TauCeti.ContinuationCocycle.quasiIso_continuationHom_iff_acyclic`: the continuation map of `ν`
  is a quasi-isomorphism if and only if the twisted complex of `ν.cone` is acyclic.
* `TauCeti.TwistingCocycle.quasiIso_blockContinuation_continuationHom_iff_acyclic`: the same for
  the off-diagonal block of a block-triangular twisting cocycle.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.9 and 1.10.
-/

public section

open CategoryTheory CochainComplex MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}

namespace ContinuationCocycle

variable {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  (ν : ContinuationCocycle mP mQ) (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0)

/-! ### The degreewise identification -/

section Components

variable (hM : IsDGRightModule h ℳ dM)

omit [Fintype P] [Fintype Q] [DirectSum.Decomposition ℳ] in
private theorem sumInl_mem {n : ℤ} {f : P ⊕ Q → M}
    (hf : f ∈ twistedTotalGrading ℳ (Sum.elim (fun x ↦ ind x + 1) indQ) n) :
    ((n + 1).negOnePow • LinearMap.funLeft R M Sum.inl) f ∈
      twistedTotalGrading ℳ ind (n + 1) := by
  refine mem_twistedTotalGrading_iff.2 fun x ↦ ?_
  have hx := mem_twistedTotalGrading_iff.1 hf (.inl x)
  rw [Sum.elim_inl, add_comm (ind x) 1, ← add_assoc] at hx
  simpa using hx

omit [Fintype P] [Fintype Q] [DirectSum.Decomposition ℳ] in
private theorem sumInr_mem {n : ℤ} {f : P ⊕ Q → M}
    (hf : f ∈ twistedTotalGrading ℳ (Sum.elim (fun x ↦ ind x + 1) indQ) n) :
    LinearMap.funLeft R M Sum.inr f ∈ twistedTotalGrading ℳ indQ n :=
  mem_twistedTotalGrading_iff.2 fun y ↦ by
    simpa using mem_twistedTotalGrading_iff.1 hf (.inr y)

omit [Fintype P] [Fintype Q] [DirectSum.Decomposition ℳ] in
private theorem ofInl_mem {n : ℤ} {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind (n + 1)) :
    ((n + 1).negOnePow • ((LinearEquiv.sumArrowLequivProdArrow P Q R M).symm.toLinearMap ∘ₗ
      LinearMap.inl R (P → M) (Q → M))) f ∈
      twistedTotalGrading ℳ (Sum.elim (fun x ↦ ind x + 1) indQ) n := by
  refine mem_twistedTotalGrading_iff.2 fun
    | .inl x => ?_
    | .inr y => by simp
  have hx := mem_twistedTotalGrading_iff.1 hf x
  rw [add_assoc, add_comm 1] at hx
  simpa using hx

omit [Fintype P] [Fintype Q] [DirectSum.Decomposition ℳ] in
private theorem ofInr_mem {n : ℤ} {g : Q → M} (hg : g ∈ twistedTotalGrading ℳ indQ n) :
    ((LinearEquiv.sumArrowLequivProdArrow P Q R M).symm.toLinearMap ∘ₗ
      LinearMap.inr R (P → M) (Q → M)) g ∈
      twistedTotalGrading ℳ (Sum.elim (fun x ↦ ind x + 1) indQ) n :=
  mem_twistedTotalGrading_iff.2 fun
    | .inl x => by simp
    | .inr y => by simpa using mem_twistedTotalGrading_iff.1 hg y

/-- The `P`-part of the cone, with the sign `(-1) ^ (n + 1)`. -/
private noncomputable def toP (n : ℤ) :
    ((ν.cone hν).twistedCochainComplex dM hM).X n ⟶ (mP.twistedCochainComplex dM hM).X (n + 1) :=
  termHom (ν.cone hν) mP hM _ n (n + 1) fun _ ↦ sumInl_mem

/-- The `Q`-part of the cone. -/
private noncomputable def toQ (n : ℤ) :
    ((ν.cone hν).twistedCochainComplex dM hM).X n ⟶ (mQ.twistedCochainComplex dM hM).X n :=
  termHom (ν.cone hν) mQ hM _ n n fun _ ↦ sumInr_mem

/-- The inclusion of the `P`-part of the cone, with the sign `(-1) ^ (n + 1)`. -/
private noncomputable def ofP (n : ℤ) :
    (mP.twistedCochainComplex dM hM).X (n + 1) ⟶ ((ν.cone hν).twistedCochainComplex dM hM).X n :=
  termHom mP (ν.cone hν) hM _ (n + 1) n fun _ ↦ ofInl_mem

/-- The inclusion of the `Q`-part of the cone. -/
private noncomputable def ofQ (n : ℤ) :
    (mQ.twistedCochainComplex dM hM).X n ⟶ ((ν.cone hν).twistedCochainComplex dM hM).X n :=
  termHom mQ (ν.cone hν) hM _ n n fun _ ↦ ofInr_mem

@[reassoc]
private theorem ofP_toP (n : ℤ) : ofP ν hν hM n ≫ toP ν hν hM n = 𝟙 _ :=
  termHom_ext fun x ↦ by
    funext p
    simp [toP, ofP]

@[reassoc]
private theorem ofP_toQ (n : ℤ) : ofP ν hν hM n ≫ toQ ν hν hM n = 0 :=
  termHom_ext fun x ↦ by
    funext q
    simp [toQ, ofP]

@[reassoc]
private theorem ofQ_toP (n : ℤ) : ofQ ν hν hM n ≫ toP ν hν hM n = 0 :=
  termHom_ext fun x ↦ by
    funext p
    simp [toP, ofQ]

@[reassoc]
private theorem ofQ_toQ (n : ℤ) : ofQ ν hν hM n ≫ toQ ν hν hM n = 𝟙 _ :=
  termHom_ext fun x ↦ by
    funext q
    simp [toQ, ofQ]

private theorem toP_ofP_add_toQ_ofQ (n : ℤ) :
    toP ν hν hM n ≫ ofP ν hν hM n + toQ ν hν hM n ≫ ofQ ν hν hM n = 𝟙 _ :=
  termHom_ext fun x ↦ by
    funext z
    cases z <;> simp [toP, ofP, toQ, ofQ]

/-- The degree-`n` identification of the twisted complex of the cone with the mapping cone. -/
private noncomputable def coneXIso (n : ℤ) :
    ((ν.cone hν).twistedCochainComplex dM hM).X n ≅ (mappingCone (ν.continuationHom hM)).X n where
  hom := toP ν hν hM n ≫ (mappingCone.inl _).v (n + 1) n (by lia) +
    toQ ν hν hM n ≫ (mappingCone.inr _).f n
  inv := (mappingCone.fst _).val.v n (n + 1) rfl ≫ ofP ν hν hM n +
    (mappingCone.snd _).v n n (add_zero n) ≫ ofQ ν hν hM n
  hom_inv_id := by
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
      Limits.zero_comp, Limits.comp_zero, add_zero, zero_add]
    exact toP_ofP_add_toQ_ofQ ν hν hM n
  inv_hom_id := by
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      ofP_toP_assoc, ofP_toQ_assoc, ofQ_toP_assoc, ofQ_toQ_assoc,
      Limits.zero_comp, Limits.comp_zero, add_zero, zero_add]
    exact mappingCone.id_X _ n (n + 1) rfl

private theorem coneXIso_hom_fst (n : ℤ) :
    (coneXIso ν hν hM n).hom ≫ (mappingCone.fst (ν.continuationHom hM)).val.v n (n + 1) rfl =
      toP ν hν hM n := by
  simp [coneXIso]

private theorem coneXIso_hom_snd (n : ℤ) :
    (coneXIso ν hν hM n).hom ≫ (mappingCone.snd (ν.continuationHom hM)).v n n (add_zero n) =
      toQ ν hν hM n := by
  simp [coneXIso]

private theorem inl_coneXIso_inv (n : ℤ) :
    (mappingCone.inl (ν.continuationHom hM)).v (n + 1) n (by lia) ≫ (coneXIso ν hν hM n).inv =
      ofP ν hν hM n := by
  simp [coneXIso]

private theorem inr_coneXIso_inv (n : ℤ) :
    (mappingCone.inr (ν.continuationHom hM)).f n ≫ (coneXIso ν hν hM n).inv = ofQ ν hν hM n := by
  simp [coneXIso]

@[reassoc]
private theorem d_toP (n : ℤ) :
    ((ν.cone hν).twistedCochainComplex dM hM).d n (n + 1) ≫ toP ν hν hM (n + 1) =
      -(toP ν hν hM n ≫ (mP.twistedCochainComplex dM hM).d (n + 1) (n + 1 + 1)) :=
  termHom_ext fun x ↦ by
    funext p
    simp [toP, twistedCochainComplexXEquiv_d, map_zsmul_unit,
      Int.negOnePow_succ]

@[reassoc]
private theorem d_toQ (n : ℤ) :
    ((ν.cone hν).twistedCochainComplex dM hM).d n (n + 1) ≫ toQ ν hν hM (n + 1) =
      toP ν hν hM n ≫ (ν.continuationHom hM).f (n + 1) +
        toQ ν hν hM n ≫ (mQ.twistedCochainComplex dM hM).d n (n + 1) :=
  termHom_ext fun x ↦ by
    -- `LinearMap.funLeft` evaluates only when fully applied; write the restrictions as lambdas.
    have hl : ∀ g : P ⊕ Q → M, LinearMap.funLeft R M Sum.inl g = fun p ↦ g (.inl p) :=
      fun g ↦ funext fun _ ↦ LinearMap.funLeft_apply ..
    have hr : ∀ g : P ⊕ Q → M, LinearMap.funLeft R M Sum.inr g = fun q ↦ g (.inr q) :=
      fun g ↦ funext fun _ ↦ LinearMap.funLeft_apply ..
    funext q
    simp only [toP, toQ, ModuleCat.hom_comp, ModuleCat.hom_add, LinearMap.comp_apply,
      LinearMap.add_apply, termHom_apply, twistedCochainComplexXEquiv_d, map_add,
      Submodule.coe_add, Pi.add_apply, continuationHom_f_apply, LinearMap.smul_apply, hl, hr,
      twistedDifferential_cone_apply_inr ν hν (twistedCochainComplexXEquiv _ _ hM n x).property,
      map_zsmul_unit, Pi.smul_apply]
    exact add_comm _ _

end Components

/-! ### The isomorphism with the mapping cone -/

section Iso

variable (hM : IsDGRightModule h ℳ dM)

/-- **The twisted complex of the cone of a continuation cocycle is the mapping cone of its
continuation map.** For a continuation cocycle `ν : mP → mQ` without entries strictly increasing
the index and a differential graded right module `(ℳ, dM)`, the twisted complex `ℳ ⊗ ⟨P ⊕ Q⟩` of
the block-triangular cocycle `ν.cone` is isomorphic to the mapping cone of the continuation map
`ℳ ⊗ ⟨P⟩ ⟶ ℳ ⊗ ⟨Q⟩` of `ν`. In degree `n` it sends `f : P ⊕ Q → M` to
`((-1) ^ (n + 1) • f ∘ inl, f ∘ inr)`. -/
noncomputable def coneTwistedCochainComplexIso :
    (ν.cone hν).twistedCochainComplex dM hM ≅ mappingCone (ν.continuationHom hM) :=
  HomologicalComplex.Hom.isoOfComponents (coneXIso ν hν hM) fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    refine mappingCone.ext_to _ (i + 1) (i + 1 + 1) rfl ?_ ?_
    · rw [Category.assoc, mappingCone.d_fst_v _ i (i + 1) (i + 1 + 1) rfl rfl]
      simp [coneXIso, d_toP_assoc]
    · rw [Category.assoc, mappingCone.d_snd_v _ i (i + 1) rfl]
      simp [coneXIso, d_toQ_assoc]

/-- The `P`-component of the isomorphism with the mapping cone in degree `n` multiplies the
`P`-part of a family by `(-1) ^ (n + 1)`. -/
@[simp]
theorem twistedCochainComplexXEquiv_fst_v_coneTwistedCochainComplexIso_hom_f_apply (n : ℤ)
    (x : ((ν.cone hν).twistedCochainComplex dM hM).X n) :
    (twistedCochainComplexXEquiv mP.mem_graded mP.twisting hM (n + 1)
        (((mappingCone.fst (ν.continuationHom hM)).val.v n (n + 1) rfl).hom
          (((ν.coneTwistedCochainComplexIso hν hM).hom.f n).hom x)) : P → M) =
      (n + 1).negOnePow • fun p ↦
        (twistedCochainComplexXEquiv (ν.cone hν).mem_graded (ν.cone hν).twisting hM n x :
          P ⊕ Q → M) (.inl p) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  simp only [coneTwistedCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    coneXIso_hom_fst]
  funext p
  simp [toP]

/-- The `Q`-component of the isomorphism with the mapping cone is the `Q`-part of a family. -/
@[simp]
theorem twistedCochainComplexXEquiv_snd_v_coneTwistedCochainComplexIso_hom_f_apply (n : ℤ)
    (x : ((ν.cone hν).twistedCochainComplex dM hM).X n) :
    (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM n
        (((mappingCone.snd (ν.continuationHom hM)).v n n (add_zero n)).hom
          (((ν.coneTwistedCochainComplexIso hν hM).hom.f n).hom x)) : Q → M) =
      fun q ↦
        (twistedCochainComplexXEquiv (ν.cone hν).mem_graded (ν.cone hν).twisting hM n x :
          P ⊕ Q → M) (.inr q) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  simp only [coneTwistedCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    coneXIso_hom_snd]
  funext q
  simp [toQ]

/-- The inverse of the isomorphism with the mapping cone sends an element `a` of degree `n + 1`
of `ℳ ⊗ ⟨P⟩` to the family `(-1) ^ (n + 1) • a` on `P`, extended by zero on `Q`. -/
@[simp]
theorem twistedCochainComplexXEquiv_coneTwistedCochainComplexIso_inv_f_inl_v_apply (n : ℤ)
    (a : (mP.twistedCochainComplex dM hM).X (n + 1)) :
    (twistedCochainComplexXEquiv (ν.cone hν).mem_graded (ν.cone hν).twisting hM n
        (((ν.coneTwistedCochainComplexIso hν hM).inv.f n).hom
          (((mappingCone.inl (ν.continuationHom hM)).v (n + 1) n (by lia)).hom a)) : P ⊕ Q → M) =
      (n + 1).negOnePow •
        Sum.elim (twistedCochainComplexXEquiv mP.mem_graded mP.twisting hM (n + 1) a : P → M)
          (0 : Q → M) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  simp only [coneTwistedCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    inl_coneXIso_inv]
  funext z
  cases z <;> simp [ofP]

/-- The inverse of the isomorphism with the mapping cone sends an element `b` of degree `n` of
`ℳ ⊗ ⟨Q⟩` to the family `b` on `Q`, extended by zero on `P`. -/
@[simp]
theorem twistedCochainComplexXEquiv_coneTwistedCochainComplexIso_inv_f_inr_f_apply (n : ℤ)
    (b : (mQ.twistedCochainComplex dM hM).X n) :
    (twistedCochainComplexXEquiv (ν.cone hν).mem_graded (ν.cone hν).twisting hM n
        (((ν.coneTwistedCochainComplexIso hν hM).inv.f n).hom
          (((mappingCone.inr (ν.continuationHom hM)).f n).hom b)) : P ⊕ Q → M) =
      Sum.elim (0 : P → M)
        (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM n b : Q → M) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  simp only [coneTwistedCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    inr_coneXIso_inv]
  funext z
  cases z <;> simp [ofQ]

/-- **The continuation map of `ν` is a quasi-isomorphism exactly when the twisted complex of
`ν.cone` is acyclic.** -/
theorem quasiIso_continuationHom_iff_acyclic :
    QuasiIso (ν.continuationHom hM) ↔ ((ν.cone hν).twistedCochainComplex dM hM).Acyclic := by
  rw [quasiIso_iff_acyclic_mappingCone]
  exact ⟨fun H i ↦ (H i).of_iso (ν.coneTwistedCochainComplexIso hν hM).symm,
    fun H i ↦ (H i).of_iso (ν.coneTwistedCochainComplexIso hν hM)⟩

end Iso

end ContinuationCocycle

namespace TwistingCocycle

/-- **The off-diagonal block of a block-triangular twisting cocycle `m` on `P ⊕ Q` induces a
quasi-isomorphism exactly when the twisted complex of `m` is acyclic.** -/
theorem quasiIso_blockContinuation_continuationHom_iff_acyclic
    (m : TwistingCocycle 𝒜 d (P ⊕ Q) (Sum.elim (fun x ↦ ind x + 1) indQ))
    (hm : ∀ x y, m.m (.inr y) (.inl x) = 0) (hM : IsDGRightModule h ℳ dM) :
    QuasiIso ((m.blockContinuation hm).continuationHom hM) ↔
      (m.twistedCochainComplex dM hM).Acyclic := by
  have := (m.blockContinuation hm).quasiIso_continuationHom_iff_acyclic
    (fun _ _ ↦ m.blockContinuation_ν_eq_zero_of_lt hm) hM
  rwa [cone_blockContinuation] at this

end TwistingCocycle

end TauCeti
