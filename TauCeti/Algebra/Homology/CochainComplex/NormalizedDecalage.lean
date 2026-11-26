/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Regular.SMul
public import TauCeti.Algebra.Homology.AddCommGrpCat.Basic

/-!
# The normalized décalage of a cochain complex of abelian groups

Let `p` be a natural number and `M` a `ℤ`-graded cochain complex of abelian groups on whose terms
multiplication by `p` is injective. The *normalized décalage* `E_p(M)` has in degree `n` the
subgroup `{x ∈ Mⁿ | d x ∈ p Mⁿ⁺¹}`, with differential `x ↦ d x / p`. Multiplication by `pⁿ`
identifies it with the subcomplex `η_p M ⊆ M[1/p]` of Berthelot–Ogus décalage,
`(η_p M)ⁿ = {x ∈ pⁿ Mⁿ | d x ∈ pⁿ⁺¹ Mⁿ⁺¹}`; the normalized form avoids the localization and
treats negative degrees in the same way as positive ones. This file works with `E_p(M)` only and
does not construct `η_p M`.

For a prime `p` this is the décalage operator Bhatt–Lurie–Mathew use to define saturated
Dieudonné complexes: a Frobenius on a `p`-torsion-free Dieudonné complex is the same as a
cochain map `M ⟶ E_p(M)`.

The cohomology of `E_p(M)` is `Hⁿ(M)` modulo its `p`-torsion. A cocycle of `E_p(M)` is the same
as a cocycle of `M`, and a cocycle `z` is a coboundary of `E_p(M)` exactly when `p • z` is a
coboundary of `M`; so sending the class of a cocycle of `M` to its class in `E_p(M)` gives a
surjection `Hⁿ(M) ⟶ Hⁿ(E_p(M))` with kernel `Hⁿ(M)[p]`, natural in `M`. Consequently `E_p`
preserves quasi-isomorphisms between complexes with `p`-torsion-free terms, the input needed to
derive it to an endofunctor of the derived category.

## Main definitions

* `CochainComplex.decalageAddSubgroup M p n`: the elements of `Mⁿ` whose differential is
  divisible by `p`.
* `CochainComplex.normalizedDecalage M p hM`: the complex `E_p(M)`.
* `CochainComplex.normalizedDecalageMap`: the cochain map `E_p(M) ⟶ E_p(N)` induced by a
  cochain map `M ⟶ N`.
* `CochainComplex.normalizedDecalageCyclesIso`: the cocycles of `E_p(M)` are those of `M`.
* `CochainComplex.homologyToNormalizedDecalage`: the map `Hⁿ(M) ⟶ Hⁿ(E_p(M))`.
* `CochainComplex.homologyNormalizedDecalageEquiv`: `Hⁿ(M) / Hⁿ(M)[p] ≃ Hⁿ(E_p(M))`.

## Main results

* `CochainComplex.decalageAddSubgroup_eq_ker`: `E_p(M)ⁿ` is the kernel of `d` followed by
  reduction modulo `p`.
* `CochainComplex.smul_normalizedDecalage_d`: `p • d_E x = d_M x`.
* `CochainComplex.normalizedDecalageMap_id`, `CochainComplex.normalizedDecalageMap_comp`:
  functoriality.
* `CochainComplex.homologyToNormalizedDecalage_surjective`,
  `CochainComplex.ker_homologyToNormalizedDecalage`: `Hⁿ(M) ⟶ Hⁿ(E_p(M))` is surjective with
  kernel `Hⁿ(M)[p]`.
* `CochainComplex.homologyMap_comp_homologyToNormalizedDecalage`: its naturality.
* `CochainComplex.quasiIso_normalizedDecalageMap`: `E_p` preserves quasi-isomorphisms.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  arXiv:1805.05501, Construction 2.1.3, Remark 2.1.4 and §7.2.
* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Publ. Math. IHÉS 128 (2018),
  arXiv:1602.03148, Lemma 6.4.
-/

public section

open CategoryTheory

universe u

namespace CochainComplex

section AddSubgroup

variable (M : CochainComplex AddCommGrpCat.{u} ℤ) (p : ℕ)

/-- The elements of `M.X n` whose differential is divisible by `p`: the degree-`n` term of the
normalized décalage `E_p(M)`. -/
def decalageAddSubgroup (n : ℤ) : AddSubgroup (M.X n) :=
  (DistribSMul.toAddMonoidHom (M.X (n + 1)) p).range.comap (M.d n (n + 1)).hom

@[simp]
lemma mem_decalageAddSubgroup_iff {n : ℤ} {x : M.X n} :
    x ∈ M.decalageAddSubgroup p n ↔ ∃ y, p • y = (M.d n (n + 1)).hom x := by
  simp [decalageAddSubgroup]

/-- `E_p(M)ⁿ` is the kernel of the differential followed by reduction modulo `p`. -/
lemma decalageAddSubgroup_eq_ker (n : ℤ) :
    M.decalageAddSubgroup p n = ((QuotientAddGroup.mk' (DistribSMul.toAddMonoidHom
      (M.X (n + 1)) p).range).comp (M.d n (n + 1)).hom).ker := by
  rw [← AddMonoidHom.comap_ker, QuotientAddGroup.ker_mk', decalageAddSubgroup]

/-- Every cocycle lies in `E_p(M)`. -/
lemma mem_decalageAddSubgroup_of_d_eq_zero {n : ℤ} {x : M.X n}
    (hx : (M.d n (n + 1)).hom x = 0) : x ∈ M.decalageAddSubgroup p n :=
  (M.mem_decalageAddSubgroup_iff p).2 ⟨0, by rw [smul_zero, hx]⟩

end AddSubgroup

variable {M : CochainComplex AddCommGrpCat.{u} ℤ} {p : ℕ} (hM : ∀ n, IsSMulRegular (M.X n) p)

/-- The map `x ↦ d x / p` on `E_p(M)ⁿ`, with values in `Mⁿ⁺¹`. -/
private noncomputable def divD (n : ℤ) : M.decalageAddSubgroup p n →+ M.X (n + 1) :=
  ((AddMonoidHom.ofInjective (f := DistribSMul.toAddMonoidHom (M.X (n + 1)) p)
    (hM (n + 1))).symm : _ →+ M.X (n + 1)).comp
      (((M.d n (n + 1)).hom.comp (M.decalageAddSubgroup p n).subtype).codRestrict _
        fun x ↦ AddSubgroup.mem_comap.1 x.property)

private lemma smul_divD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    p • divD hM n x = (M.d n (n + 1)).hom x :=
  AddMonoidHom.apply_ofInjective_symm (f := DistribSMul.toAddMonoidHom (M.X (n + 1)) p)
    (hM (n + 1)) _

private lemma d_divD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    (M.d (n + 1) (n + 1 + 1)).hom (divD hM n x) = 0 := by
  refine hM (n + 1 + 1) ?_
  beta_reduce
  rw [smul_zero, ← map_nsmul, smul_divD, ← AddCommGrpCat.comp_apply, M.d_comp_d]
  simp

/-- The differential `x ↦ d x / p` of the normalized décalage. -/
noncomputable def decalageD (n : ℤ) :
    M.decalageAddSubgroup p n →+ M.decalageAddSubgroup p (n + 1) :=
  (divD hM n).codRestrict _ fun x ↦ M.mem_decalageAddSubgroup_of_d_eq_zero p (d_divD hM n x)

/-- The defining property of `decalageD`: `p • d_E x = d x`. -/
lemma smul_decalageD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    p • (decalageD hM n x : M.X (n + 1)) = (M.d n (n + 1)).hom x :=
  smul_divD hM n x

/-- `decalageD hM n x` is the unique `y` with `p • y = d x`. -/
lemma decalageD_eq_iff {n : ℤ} {x : M.decalageAddSubgroup p n} {y : M.X (n + 1)} :
    (decalageD hM n x : M.X (n + 1)) = y ↔ p • y = (M.d n (n + 1)).hom x :=
  ⟨fun h ↦ h ▸ smul_decalageD hM n x, fun h ↦ hM (n + 1) ((smul_decalageD hM n x).trans h.symm)⟩

/-- The image of the differential of `E_p(M)` consists of cocycles of `M`. -/
@[simp]
lemma d_decalageD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    (M.d (n + 1) (n + 1 + 1)).hom (decalageD hM n x) = 0 :=
  d_divD hM n x

/-- The differential of the normalized décalage squares to zero. -/
lemma decalageD_comp_decalageD (n : ℤ) :
    (decalageD hM (n + 1)).comp (decalageD hM n) = 0 := by
  ext x
  exact (decalageD_eq_iff hM).2 (by simp)

variable (M p) in
/-- The normalized décalage `E_p(M)` of a cochain complex of abelian groups on whose terms
multiplication by `p` is injective: the elements `x` with `d x` divisible by `p`, with
differential `x ↦ d x / p`. -/
noncomputable abbrev normalizedDecalage : CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.of (fun n ↦ AddCommGrpCat.of (M.decalageAddSubgroup p n))
    (fun n ↦ AddCommGrpCat.ofHom (decalageD hM n))
    (fun n ↦ by ext1; exact decalageD_comp_decalageD hM n)

lemma normalizedDecalage_d_apply (n : ℤ) (x : M.decalageAddSubgroup p n) :
    ((M.normalizedDecalage p hM).d n (n + 1)).hom x = decalageD hM n x := by
  simp only [normalizedDecalage, CochainComplex.of_d, AddCommGrpCat.hom_ofHom]

/-- The differential of `E_p(M)` multiplied by `p` is the differential of `M`. -/
lemma smul_normalizedDecalage_d (i j : ℤ) (x : M.decalageAddSubgroup p i) :
    p • Subtype.val (((M.normalizedDecalage p hM).d i j).hom x) = (M.d i j).hom x := by
  by_cases hij : i + 1 = j
  · subst hij
    rw [normalizedDecalage_d_apply, smul_decalageD]
  · rw [(M.normalizedDecalage p hM).shape i j hij, M.shape i j hij]
    simp

section Map

variable {N : CochainComplex AddCommGrpCat.{u} ℤ} (hN : ∀ n, IsSMulRegular (N.X n) p)

/-- A cochain map sends `E_p(M)` into `E_p(N)`. -/
lemma map_mem_decalageAddSubgroup (φ : M ⟶ N) {n : ℤ} {x : M.X n}
    (hx : x ∈ M.decalageAddSubgroup p n) : (φ.f n).hom x ∈ N.decalageAddSubgroup p n := by
  obtain ⟨y, hy⟩ := (M.mem_decalageAddSubgroup_iff p).1 hx
  refine (N.mem_decalageAddSubgroup_iff p).2 ⟨(φ.f (n + 1)).hom y, ?_⟩
  rw [← map_nsmul, hy, ← AddCommGrpCat.comp_apply, ← φ.comm, AddCommGrpCat.comp_apply]

/-- The degree-`n` component of `normalizedDecalageMap`. -/
private noncomputable def normalizedDecalageMapF (φ : M ⟶ N) (n : ℤ) :
    (M.normalizedDecalage p hM).X n ⟶ (N.normalizedDecalage p hN).X n :=
  AddCommGrpCat.ofHom
    (((φ.f n).hom.comp (M.decalageAddSubgroup p n).subtype).codRestrict _
      fun x ↦ map_mem_decalageAddSubgroup φ x.property)

private lemma normalizedDecalageMapF_apply (φ : M ⟶ N) (n : ℤ)
    (x : (M.normalizedDecalage p hM).X n) :
    Subtype.val ((normalizedDecalageMapF hM hN φ n).hom x) = (φ.f n).hom x.val :=
  rfl

/-- The cochain map `E_p(M) ⟶ E_p(N)` induced by a cochain map `M ⟶ N`: it is `φ` on
elements. -/
noncomputable def normalizedDecalageMap (φ : M ⟶ N) :
    M.normalizedDecalage p hM ⟶ N.normalizedDecalage p hN :=
  CochainComplex.ofHom (normalizedDecalageMapF hM hN φ) fun n ↦ by
    ext x
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    rw [normalizedDecalage_d_apply, decalageD_eq_iff, normalizedDecalageMapF_apply,
      normalizedDecalageMapF_apply, ← map_nsmul, smul_normalizedDecalage_d,
      ← AddCommGrpCat.comp_apply, ← φ.comm, AddCommGrpCat.comp_apply]

@[simp]
lemma normalizedDecalageMap_f_apply (φ : M ⟶ N) (n : ℤ) (x : M.decalageAddSubgroup p n) :
    Subtype.val (((normalizedDecalageMap hM hN φ).f n).hom x) = (φ.f n).hom x :=
  (rfl)

@[simp]
lemma normalizedDecalageMap_id : normalizedDecalageMap hM hM (𝟙 M) = 𝟙 _ := by
  ext n x
  rfl

@[simp]
lemma normalizedDecalageMap_comp {K : CochainComplex AddCommGrpCat.{u} ℤ}
    (hK : ∀ n, IsSMulRegular (K.X n) p) (φ : M ⟶ N) (ψ : N ⟶ K) :
    normalizedDecalageMap hM hK (φ ≫ ψ) =
      normalizedDecalageMap hM hN φ ≫ normalizedDecalageMap hN hK ψ := by
  ext n x
  rfl

end Map

section Homology

/-- The inclusion `E_p(M)ⁿ ⊆ Mⁿ`, as a morphism of abelian groups. It is not a cochain map. -/
private noncomputable abbrev decalageι (n : ℤ) : (M.normalizedDecalage p hM).X n ⟶ M.X n :=
  AddCommGrpCat.ofHom (M.decalageAddSubgroup p n).subtype

/-- An element of `Mʲ` is `d_E` of an element of `E_p(M)ⁱ` exactly when `p` times it is `d` of an
element of `Mⁱ`. -/
private lemma exists_normalizedDecalage_d_eq_iff {i j : ℤ} (hij : i + 1 = j) (z : M.X j) :
    (∃ y : (M.normalizedDecalage p hM).X i,
      Subtype.val (((M.normalizedDecalage p hM).d i j).hom y) = z) ↔
      ∃ y : M.X i, (M.d i j).hom y = p • z := by
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨y.val, by rw [← smul_normalizedDecalage_d hM, hy]⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  subst hij
  refine ⟨⟨y, (M.mem_decalageAddSubgroup_iff p).2 ⟨z, hy.symm⟩⟩, hM (i + 1) ?_⟩
  beta_reduce
  rw [smul_normalizedDecalage_d hM, hy]

/-- A cocycle of `M` lies in `E_p(M)`, as a morphism of abelian groups. -/
private noncomputable def cyclesToNormalizedDecalage (n : ℤ) :
    M.cycles n ⟶ (M.normalizedDecalage p hM).X n :=
  AddCommGrpCat.ofHom (X := M.cycles n) ((M.iCycles n).hom.codRestrict _ fun z ↦
    M.mem_decalageAddSubgroup_of_d_eq_zero p (M.addCommGrpCat_d_iCycles_apply n (n + 1) z))

private lemma cyclesToNormalizedDecalage_apply (n : ℤ) (z : M.cycles n) :
    Subtype.val ((cyclesToNormalizedDecalage hM n).hom z) = (M.iCycles n).hom z :=
  rfl

variable (p) in
/-- The cocycles of the normalized décalage `E_p(M)` are the cocycles of `M`: an element of
`E_p(M)ⁿ` is killed by `d / p` exactly when it is killed by `d`. -/
noncomputable def normalizedDecalageCyclesIso (n : ℤ) :
    (M.normalizedDecalage p hM).cycles n ≅ M.cycles n where
  hom := M.liftCycles ((M.normalizedDecalage p hM).iCycles n ≫ decalageι hM n) (n + 1) (by simp)
    (by
      ext z
      simp only [Category.assoc, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
        AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply, AddCommGrpCat.hom_ofHom,
        AddSubgroup.coe_subtype]
      rw [← smul_normalizedDecalage_d hM, HomologicalComplex.addCommGrpCat_d_iCycles_apply]
      simp)
  inv := (M.normalizedDecalage p hM).liftCycles (cyclesToNormalizedDecalage hM n) (n + 1) (by simp)
    (by
      refine AddCommGrpCat.ext fun z ↦ Subtype.ext (hM (n + 1) ?_)
      beta_reduce
      rw [AddCommGrpCat.comp_apply, smul_normalizedDecalage_d hM,
        cyclesToNormalizedDecalage_apply]
      simp)
  hom_inv_id := by
    rw [← cancel_mono ((M.normalizedDecalage p hM).iCycles n), Category.assoc,
      HomologicalComplex.liftCycles_i, Category.id_comp]
    ext z
    rw [AddCommGrpCat.comp_apply, cyclesToNormalizedDecalage_apply, ← AddCommGrpCat.comp_apply,
      HomologicalComplex.liftCycles_i, AddCommGrpCat.comp_apply]
    simp
  inv_hom_id := by
    rw [← cancel_mono (M.iCycles n), Category.assoc, HomologicalComplex.liftCycles_i,
      Category.id_comp, ← Category.assoc, HomologicalComplex.liftCycles_i]
    ext z
    rw [AddCommGrpCat.comp_apply, ← cyclesToNormalizedDecalage_apply hM]
    simp

/-- `normalizedDecalageCyclesIso` does not change the underlying element of a cocycle. -/
@[simp]
lemma iCycles_normalizedDecalageCyclesIso_hom_apply (n : ℤ)
    (z : (M.normalizedDecalage p hM).cycles n) :
    (M.iCycles n).hom ((M.normalizedDecalageCyclesIso p hM n).hom.hom z) =
      Subtype.val (((M.normalizedDecalage p hM).iCycles n).hom z) := by
  rw [← AddCommGrpCat.comp_apply]
  simp [normalizedDecalageCyclesIso]

/-- The inverse of `normalizedDecalageCyclesIso` does not change the underlying element of a
cocycle. -/
@[simp]
lemma iCycles_normalizedDecalageCyclesIso_inv_apply (n : ℤ) (z : M.cycles n) :
    Subtype.val (((M.normalizedDecalage p hM).iCycles n).hom
      ((M.normalizedDecalageCyclesIso p hM n).inv.hom z)) = (M.iCycles n).hom z := by
  rw [← AddCommGrpCat.comp_apply]
  simp only [normalizedDecalageCyclesIso, HomologicalComplex.liftCycles_i]
  exact cyclesToNormalizedDecalage_apply hM n z

/-- A cocycle `z` of `M` has zero class in the cohomology of `E_p(M)` exactly when `p • z` is a
coboundary of `M`. -/
lemma homologyπ_normalizedDecalageCyclesIso_inv_apply_eq_zero_iff {i n : ℤ} (hin : i + 1 = n)
    (z : M.cycles n) :
    ((M.normalizedDecalage p hM).homologyπ n).hom
      ((M.normalizedDecalageCyclesIso p hM n).inv.hom z) = 0 ↔
      ∃ y : M.X i, (M.d i n).hom y = p • (M.iCycles n).hom z := by
  rw [HomologicalComplex.addCommGrpCat_homologyπ_eq_zero_iff _
      (by rw [CochainComplex.prev, ← hin, add_sub_cancel_right]),
    ← exists_normalizedDecalage_d_eq_iff hM hin]
  refine exists_congr fun y ↦ ?_
  rw [← iCycles_normalizedDecalageCyclesIso_inv_apply hM n z, Subtype.ext_iff]

variable (p) in
/-- The map `Hⁿ(M) ⟶ Hⁿ(E_p(M))` sending the class of a cocycle of `M` to its class as a cocycle
of the normalized décalage `E_p(M)`. It is surjective, with kernel the `p`-torsion of `Hⁿ(M)`. -/
noncomputable def homologyToNormalizedDecalage (n : ℤ) :
    M.homology n ⟶ (M.normalizedDecalage p hM).homology n :=
  (M.homologyIsCokernel (n - 1) n (CochainComplex.prev ℤ n)).desc (Limits.CokernelCofork.ofπ
    ((M.normalizedDecalageCyclesIso p hM n).inv ≫ (M.normalizedDecalage p hM).homologyπ n) (by
      refine AddCommGrpCat.ext fun y ↦ ?_
      rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, AddCommGrpCat.zero_apply,
        homologyπ_normalizedDecalageCyclesIso_inv_apply_eq_zero_iff hM (sub_add_cancel n 1),
        HomologicalComplex.addCommGrpCat_iCycles_toCycles_apply]
      exact ⟨p • y, map_nsmul _ _ _⟩))

/-- `homologyToNormalizedDecalage` sends the class of a cocycle of `M` to the class of the same
cocycle of `E_p(M)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_homologyToNormalizedDecalage (n : ℤ) :
    M.homologyπ n ≫ M.homologyToNormalizedDecalage p hM n =
      (M.normalizedDecalageCyclesIso p hM n).inv ≫ (M.normalizedDecalage p hM).homologyπ n :=
  Limits.Cofork.IsColimit.π_desc (M.homologyIsCokernel (n - 1) n (CochainComplex.prev ℤ n))

/-- The class of a cocycle of `M` is sent to its class in the cohomology of `E_p(M)`. -/
@[simp]
lemma homologyToNormalizedDecalage_homologyπ_apply (n : ℤ) (z : M.cycles n) :
    (M.homologyToNormalizedDecalage p hM n).hom ((M.homologyπ n).hom z) =
      ((M.normalizedDecalage p hM).homologyπ n).hom
        ((M.normalizedDecalageCyclesIso p hM n).inv.hom z) := by
  rw [← AddCommGrpCat.comp_apply, homologyπ_homologyToNormalizedDecalage, AddCommGrpCat.comp_apply]

/-- Every cohomology class of `E_p(M)` is the class of a cocycle of `M`. -/
lemma homologyToNormalizedDecalage_surjective (n : ℤ) :
    Function.Surjective (M.homologyToNormalizedDecalage p hM n).hom := by
  intro x
  obtain ⟨z, rfl⟩ := HomologicalComplex.addCommGrpCat_homologyπ_surjective _ n x
  exact ⟨(M.homologyπ n).hom ((M.normalizedDecalageCyclesIso p hM n).hom.hom z), by
    rw [homologyToNormalizedDecalage_homologyπ_apply, Iso.hom_inv_id_apply]⟩

/-- The kernel of `Hⁿ(M) ⟶ Hⁿ(E_p(M))` is the `p`-torsion of `Hⁿ(M)`. -/
lemma homologyToNormalizedDecalage_apply_eq_zero_iff {n : ℤ} (x : M.homology n) :
    (M.homologyToNormalizedDecalage p hM n).hom x = 0 ↔ p • x = 0 := by
  obtain ⟨z, rfl⟩ := HomologicalComplex.addCommGrpCat_homologyπ_surjective _ n x
  rw [homologyToNormalizedDecalage_homologyπ_apply,
    homologyπ_normalizedDecalageCyclesIso_inv_apply_eq_zero_iff hM (sub_add_cancel n 1),
    ← map_nsmul (M.homologyπ n).hom,
    HomologicalComplex.addCommGrpCat_homologyπ_eq_zero_iff _ (CochainComplex.prev ℤ n), map_nsmul]

/-- The kernel of `Hⁿ(M) ⟶ Hⁿ(E_p(M))` is the `p`-torsion subgroup `Hⁿ(M)[p]`. -/
lemma ker_homologyToNormalizedDecalage (n : ℤ) :
    (M.homologyToNormalizedDecalage p hM n).hom.ker = AddSubgroup.torsionBy (M.homology n) p := by
  ext x
  rw [AddMonoidHom.mem_ker, homologyToNormalizedDecalage_apply_eq_zero_iff,
    AddSubgroup.torsionBy.nsmul_iff]

variable (p) in
/-- The cohomology of the normalized décalage: `Hⁿ(M) / Hⁿ(M)[p] ≃ Hⁿ(E_p(M))`, induced by sending
a cocycle of `M` to its class as a cocycle of `E_p(M)`. -/
noncomputable def homologyNormalizedDecalageEquiv (n : ℤ) :
    (M.homology n ⧸ AddSubgroup.torsionBy (M.homology n) p) ≃+
      (M.normalizedDecalage p hM).homology n :=
  (QuotientAddGroup.quotientAddEquivOfEq (M.ker_homologyToNormalizedDecalage hM n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (M.homologyToNormalizedDecalage_surjective hM n))

/-- `homologyNormalizedDecalageEquiv` sends the class of `x` modulo `p`-torsion to the image of
`x` under `homologyToNormalizedDecalage`. -/
@[simp]
lemma homologyNormalizedDecalageEquiv_mk {n : ℤ} (x : M.homology n) :
    M.homologyNormalizedDecalageEquiv p hM n x = (M.homologyToNormalizedDecalage p hM n).hom x := by
  simp [homologyNormalizedDecalageEquiv, QuotientAddGroup.quotientKerEquivOfSurjective]

section Naturality

variable {N : CochainComplex AddCommGrpCat.{u} ℤ} (hN : ∀ n, IsSMulRegular (N.X n) p)

/-- The identification of the cocycles of `E_p(M)` with those of `M` is natural in `M`. -/
@[reassoc]
lemma cyclesMap_comp_normalizedDecalageCyclesIso_inv (φ : M ⟶ N) (n : ℤ) :
    HomologicalComplex.cyclesMap φ n ≫ (N.normalizedDecalageCyclesIso p hN n).inv =
      (M.normalizedDecalageCyclesIso p hM n).inv ≫
        HomologicalComplex.cyclesMap (normalizedDecalageMap hM hN φ) n := by
  ext z
  refine HomologicalComplex.addCommGrpCat_iCycles_injective _ n (Subtype.ext ?_)
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
    iCycles_normalizedDecalageCyclesIso_inv_apply,
    HomologicalComplex.addCommGrpCat_iCycles_cyclesMap_apply,
    HomologicalComplex.addCommGrpCat_iCycles_cyclesMap_apply, normalizedDecalageMap_f_apply,
    iCycles_normalizedDecalageCyclesIso_inv_apply]

/-- The map `Hⁿ(M) ⟶ Hⁿ(E_p(M))` is natural in `M`. -/
@[reassoc, elementwise]
lemma homologyMap_comp_homologyToNormalizedDecalage (φ : M ⟶ N) (n : ℤ) :
    HomologicalComplex.homologyMap φ n ≫ N.homologyToNormalizedDecalage p hN n =
      M.homologyToNormalizedDecalage p hM n ≫
        HomologicalComplex.homologyMap (normalizedDecalageMap hM hN φ) n := by
  rw [← cancel_epi (M.homologyπ n), HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_homologyToNormalizedDecalage, homologyπ_homologyToNormalizedDecalage_assoc,
    cyclesMap_comp_normalizedDecalageCyclesIso_inv_assoc hM hN,
    HomologicalComplex.homologyπ_naturality]

/-- The normalized décalage preserves quasi-isomorphisms in each degree. -/
instance quasiIsoAt_normalizedDecalageMap (φ : M ⟶ N) (n : ℤ) [QuasiIsoAt φ n] :
    QuasiIsoAt (normalizedDecalageMap hM hN φ) n := by
  have hφ := (ConcreteCategory.isIso_iff_bijective (HomologicalComplex.homologyMap φ n)).1
    ((quasiIsoAt_iff_isIso_homologyMap φ n).1 inferInstance)
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := M.homologyToNormalizedDecalage_surjective hM n x
    rw [← homologyMap_comp_homologyToNormalizedDecalage_apply,
      homologyToNormalizedDecalage_apply_eq_zero_iff, ← map_nsmul] at hx
    rw [homologyToNormalizedDecalage_apply_eq_zero_iff]
    exact hφ.1 (hx.trans (map_zero _).symm)
  · obtain ⟨y, rfl⟩ := N.homologyToNormalizedDecalage_surjective hN n y
    obtain ⟨x, rfl⟩ := hφ.2 y
    exact ⟨_, (homologyMap_comp_homologyToNormalizedDecalage_apply hM hN φ n x).symm⟩

/-- The normalized décalage preserves quasi-isomorphisms. -/
instance quasiIso_normalizedDecalageMap (φ : M ⟶ N) [QuasiIso φ] :
    QuasiIso (normalizedDecalageMap hM hN φ) where
  quasiIsoAt _ := inferInstance

end Naturality

end Homology

end CochainComplex
