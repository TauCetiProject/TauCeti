/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.Algebra.Homology.CochainComplex.NormalizedDecalage

/-!
# Dieudonné complexes

A *Dieudonné complex* (Bhatt–Lurie–Mathew) for a natural number `p` (in practice a prime) is a
`ℤ`-graded cochain complex of abelian groups `(M, d)` together with a map of graded abelian groups
`F : M → M`, the Frobenius, satisfying `d (F x) = p • F (d x)`. A morphism of Dieudonné complexes
is a cochain map commuting with the Frobenius.

When the terms of `M` are `p`-torsion-free, a Frobenius is the same thing as a cochain map
`M ⟶ E_p(M)` into the normalized décalage, `x ↦ F x`: the relation `d (F x) = p • F (d x)` says
exactly that `F x` lies in `E_p(M)` and that `F` commutes with `d` and `d_E = d / p`. In the
coordinates of Bhatt–Lurie–Mathew this is the map `α_F : M → η_p M`, `x ↦ pⁿ F x` in degree `n`.

Dieudonné complexes are the starting point of the construction of the de Rham–Witt complex as the
strict completion of the saturation of a Dieudonné complex.

## Main definitions

* `TauCeti.DieudonneComplex p`: a Dieudonné complex.
* `TauCeti.DieudonneComplex.Hom`: morphisms of Dieudonné complexes; these form a category.
* `TauCeti.DieudonneComplex.forget`: the forgetful functor to cochain complexes.
* `TauCeti.DieudonneComplex.toNormalizedDecalage`: the cochain map `α_F : M ⟶ E_p(M)`.
* `TauCeti.DieudonneComplex.ofNormalizedDecalage`: the Dieudonné complex with Frobenius given by
  a cochain map `M ⟶ E_p(M)`.

## Main results

* `TauCeti.DieudonneComplex.isIso_iff_bijective`: a morphism of Dieudonné complexes is an
  isomorphism iff it is bijective in every degree.
* `TauCeti.DieudonneComplex.toNormalizedDecalage_ofNormalizedDecalage` and
  `TauCeti.DieudonneComplex.ofNormalizedDecalage_toNormalizedDecalage`: on `p`-torsion-free
  complexes, Frobenius structures and cochain maps into the normalized décalage correspond.
* `TauCeti.DieudonneComplex.toNormalizedDecalage_naturality`: `α_F` is natural.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  arXiv:1805.05501, Definition 2.1.1, Construction 2.1.3 and Remark 2.1.4.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

/-- A Dieudonné complex: a `ℤ`-graded cochain complex of abelian groups `M` with a map of graded
abelian groups `F : M → M`, the Frobenius, such that `d (F x) = p • F (d x)`. -/
structure DieudonneComplex (p : ℕ) extends
    toCochainComplex : CochainComplex AddCommGrpCat.{u} ℤ where
  /-- The Frobenius, a map of graded abelian groups. -/
  F (n : ℤ) : X n ⟶ X n
  /-- The Frobenius relation `d F = p F d`. -/
  d_F (n : ℤ) (x : X n) :
    (d n (n + 1)).hom ((F n).hom x) = p • (F (n + 1)).hom ((d n (n + 1)).hom x)

namespace DieudonneComplex

variable {p : ℕ}

section Basic

variable (M : DieudonneComplex.{u} p)

/-- The Frobenius relation `d F = p F d` for the differential between any two degrees. -/
lemma d_F_apply (i j : ℤ) (x : M.X i) :
    (M.d i j).hom ((M.F i).hom x) = p • (M.F j).hom ((M.d i j).hom x) := by
  obtain rfl | h := eq_or_ne (i + 1) j
  · exact M.d_F i x
  · simp [M.shape i j h]

/-- The iterated Frobenius relation `d Fʳ = pʳ Fʳ d`. -/
lemma d_F_iterate_apply (n : ℤ) (r : ℕ) (x : M.X n) :
    (M.d n (n + 1)).hom ((⇑(M.F n).hom)^[r] x) =
      p ^ r • (⇑(M.F (n + 1)).hom)^[r] ((M.d n (n + 1)).hom x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', M.d_F, ih, map_nsmul,
      pow_succ', mul_smul]

end Basic

/-- A morphism of Dieudonné complexes: a cochain map commuting with the Frobenius. -/
@[ext]
structure Hom (M N : DieudonneComplex.{u} p) where
  /-- The underlying cochain map. -/
  hom : M.toCochainComplex ⟶ N.toCochainComplex
  /-- Compatibility with the Frobenius. -/
  comm_F (n : ℤ) : M.F n ≫ hom.f n = hom.f n ≫ N.F n

attribute [reassoc] Hom.comm_F

instance : Category (DieudonneComplex.{u} p) where
  Hom := Hom
  id M := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, fun n ↦ by simp [f.comm_F_assoc, g.comm_F]⟩

variable {M N K : DieudonneComplex.{u} p}

@[ext]
lemma hom_ext {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma id_hom (M : DieudonneComplex.{u} p) : (𝟙 M : M ⟶ M).hom = 𝟙 _ :=
  rfl

@[simp, reassoc]
lemma comp_hom (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- A morphism of Dieudonné complexes commutes with the Frobenius, on elements. -/
lemma Hom.comm_F_apply (f : M ⟶ N) (n : ℤ) (x : M.X n) :
    (f.hom.f n).hom ((M.F n).hom x) = (N.F n).hom ((f.hom.f n).hom x) := by
  rw [← AddCommGrpCat.comp_apply, f.comm_F, AddCommGrpCat.comp_apply]

variable (p) in
/-- The forgetful functor from Dieudonné complexes to cochain complexes. -/
@[expose, simps]
def forget : DieudonneComplex.{u} p ⥤ CochainComplex AddCommGrpCat.{u} ℤ where
  obj M := M.toCochainComplex
  map f := f.hom

instance : (forget.{u} p).Faithful where
  map_injective h := hom_ext h

/-- A morphism of Dieudonné complexes is an isomorphism iff it is bijective in every degree. -/
lemma isIso_iff_bijective (f : M ⟶ N) : IsIso f ↔ ∀ n, Function.Bijective (f.hom.f n).hom := by
  refine ⟨fun _ n ↦ ConcreteCategory.bijective_of_isIso ((forget p).map f |>.f n), fun h ↦ ?_⟩
  have (n : ℤ) : IsIso (f.hom.f n) := (ConcreteCategory.isIso_iff_bijective _).2 (h n)
  have : IsIso f.hom := HomologicalComplex.Hom.isIso_of_components f.hom
  refine ⟨⟨inv f.hom, fun n ↦ ?_⟩, hom_ext (by simp), hom_ext (by simp)⟩
  rw [← cancel_mono (f.hom.f n)]
  simp [HomologicalComplex.Hom.inv_f_apply, f.comm_F]

instance : (forget.{u} p).ReflectsIsomorphisms where
  reflects f _ := (isIso_iff_bijective f).2 fun n ↦
    ConcreteCategory.bijective_of_isIso ((forget p).map f |>.f n)

section Decalage

open CochainComplex

/-- The Frobenius of a Dieudonné complex takes values in the normalized décalage `E_p(M)`. -/
lemma F_mem_decalageAddSubgroup (M : DieudonneComplex.{u} p) (n : ℤ) (x : M.X n) :
    (M.F n).hom x ∈ decalageAddSubgroup M.toCochainComplex p n :=
  (mem_decalageAddSubgroup_iff _ _).2 ⟨_, (M.d_F n x).symm⟩

variable (M) (hM : ∀ n, IsSMulRegular (M.X n) p)

/-- The degree-`n` component of `toNormalizedDecalage`. -/
private noncomputable def toNormalizedDecalageF (n : ℤ) :
    M.X n ⟶ (normalizedDecalage M.toCochainComplex p hM).X n :=
  AddCommGrpCat.ofHom ((M.F n).hom.codRestrict _ (M.F_mem_decalageAddSubgroup n))

/-- The Frobenius of a `p`-torsion-free Dieudonné complex as a cochain map `α_F : M ⟶ E_p(M)`
into the normalized décalage, `x ↦ F x`. -/
noncomputable def toNormalizedDecalage :
    M.toCochainComplex ⟶ normalizedDecalage M.toCochainComplex p hM :=
  CochainComplex.ofHom (toNormalizedDecalageF M hM) fun n ↦ by
    ext x
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
      AddMonoidHom.comp_apply, normalizedDecalage_d_apply, decalageD_eq_iff]
    exact (M.d_F n x).symm

@[simp]
lemma toNormalizedDecalage_f_apply (n : ℤ) (x : M.X n) :
    Subtype.val (((M.toNormalizedDecalage hM).f n).hom x) = (M.F n).hom x :=
  (rfl)

/-- The Dieudonné complex structure on a `p`-torsion-free cochain complex `K` whose Frobenius is
given by a cochain map `α : K ⟶ E_p(K)` into the normalized décalage. -/
@[expose, simps toCochainComplex]
noncomputable def ofNormalizedDecalage (K : CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : ∀ n, IsSMulRegular (K.X n) p) (α : K ⟶ K.normalizedDecalage p hK) :
    DieudonneComplex.{u} p where
  toCochainComplex := K
  F n := AddCommGrpCat.ofHom ((K.decalageAddSubgroup p n).subtype.comp (α.f n).hom)
  d_F n x := by
    simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype]
    rw [← smul_normalizedDecalage_d hK, ← AddCommGrpCat.comp_apply, α.comm,
      AddCommGrpCat.comp_apply]

@[simp]
lemma ofNormalizedDecalage_F_apply (K : CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : ∀ n, IsSMulRegular (K.X n) p) (α : K ⟶ K.normalizedDecalage p hK) (n : ℤ) (x : K.X n) :
    ((ofNormalizedDecalage K hK α).F n).hom x = Subtype.val ((α.f n).hom x) :=
  rfl

/-- The cochain map into the normalized décalage of the Dieudonné complex defined by `α` is
`α`. -/
@[simp]
lemma toNormalizedDecalage_ofNormalizedDecalage (K : CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : ∀ n, IsSMulRegular (K.X n) p) (α : K ⟶ K.normalizedDecalage p hK) :
    (ofNormalizedDecalage K hK α).toNormalizedDecalage hK = α := by
  ext n x
  exact (toNormalizedDecalage_f_apply _ hK n x).trans (ofNormalizedDecalage_F_apply K hK α n x)

/-- The Dieudonné complex defined by the cochain map `α_F` is the original one. -/
@[simp]
lemma ofNormalizedDecalage_toNormalizedDecalage :
    ofNormalizedDecalage M.toCochainComplex hM (M.toNormalizedDecalage hM) = M := by
  obtain ⟨K, F, d_F⟩ := M
  congr

/-- `α_F` is natural in morphisms of `p`-torsion-free Dieudonné complexes. -/
@[reassoc]
lemma toNormalizedDecalage_naturality (hN : ∀ n, IsSMulRegular (N.X n) p) (f : M ⟶ N) :
    M.toNormalizedDecalage hM ≫ normalizedDecalageMap hM hN f.hom =
      f.hom ≫ N.toNormalizedDecalage hN := by
  ext n x
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, AddCommGrpCat.comp_apply,
    AddCommGrpCat.comp_apply, normalizedDecalageMap_f_apply, toNormalizedDecalage_f_apply,
    toNormalizedDecalage_f_apply, Hom.comm_F_apply]

end Decalage

end DieudonneComplex

end TauCeti
