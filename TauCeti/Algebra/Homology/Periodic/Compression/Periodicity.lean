/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.Shift
public import TauCeti.CategoryTheory.Shift.OrbitCategory

/-!
# Periodicity of compression

The `n`-periodic compression `Δₙ` is invariant under shifting by a multiple `k` of `n`: there is
a natural isomorphism `Δₙ (K⟦k⟧) ≅ Δₙ K`. In residue degree `r`, it sends the summand
`(K⟦k⟧)^i = K^(i+k)` to the summand of degree `i + k` of `Δₙ K`, which lies in the same residue
class, with the sign `(-1)^(k * i)`. The sign compensates for the factor `(-1)^k` on the
differential of `K⟦k⟧`, so it is needed exactly when `k` is odd.

This is not the composite of `compressionShiftIso` with a periodicity isomorphism of
`ZMod n`-graded complexes: for odd `n`, the shift by `n` of a periodic complex has the negated
differential and need not be isomorphic to it. The sign `(-1)^(k * i)` depends on the integer
degree `i`, which the compression still remembers summand by summand.

The isomorphism is natural, so it gives the periodicity isomorphism
`[k] ⋙ Δₙ ≅ Δₙ` of the compression functor on bounded complexes, and, along the localization
functor to the bounded homotopy category, of the compression functor `K^b(C) ⥤ K_n(C)`. Taking
`k = n`, Keller's universal property of the orbit category descends compression to the orbit
functor `K^b(C)/[n] ⥤ K_n(C)` (`TauCeti.PeriodicComplex.orbitCompressionFunctor`).

The periodicity isomorphisms for shifts by `a`, `b` and `a + b` are compatible with the
identification `K⟦a + b⟧ ≅ K⟦a⟧⟦b⟧` only up to the sign `(-1)^(a * b)`
(`TauCeti.PeriodicComplex.homotopyCompressionFunctorPeriodicityIso_shiftComp_hom_app`), since the
summand of degree `i` acquires `(-1)^(b * i) * (-1)^(a * (i + b))` on one side and
`(-1)^((a + b) * i)` on the other. The one for the shift by `0` is the identification `X⟦0⟧ ≅ X`.
Hence the powers of the periodicity isomorphism for the shift by `n`, which define the action of
the orbit functor on morphisms, are the periodicity isomorphisms for the shifts by multiples of
`n` up to signs.

## Main definitions

* `TauCeti.PeriodicComplex.compressionPeriodicityIso`: the isomorphism
  `Δₙ (K⟦k⟧) ≅ Δₙ K` for `k` divisible by `n`.
* `TauCeti.PeriodicComplex.compressionFunctorPeriodicityIso`: its version for the compression
  functor on bounded complexes.
* `TauCeti.PeriodicComplex.homotopyCompressionFunctorPeriodicityIso`: its version for the
  compression functor `K^b(C) ⥤ K_n(C)` on homotopy categories.
* `TauCeti.PeriodicComplex.orbitCompressionFunctor`: the orbit functor `K^b(C)/[n] ⥤ K_n(C)`.

## Main results

* `TauCeti.PeriodicComplex.compressionPeriodicityIso_add_hom`: the periodicity isomorphisms compose
  up to the sign `(-1)^(a * b)`.
* `TauCeti.PeriodicComplex.homotopyCompressionFunctorPeriodicityIso_shiftComp_hom_app`: the same
  for the compression functor `K^b(C) ⥤ K_n(C)`.

## References

* B. Keller, *On triangulated orbit categories*, Documenta Mathematica **10** (2005),
  551–581, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
* `compressionFunctorPeriodicityIso` on bounded complexes is assembled like
  `TauCeti.PeriodicComplex.compressionFunctorShiftIso`, from their shared comparison
  `TauCeti.PeriodicComplex.shiftCompCompressionFunctorIso`
  (`TauCeti.Algebra.Homology.Periodic.Compression.Shift`), and the descent of
  `homotopyCompressionFunctorPeriodicityIso` along the localization functor follows the
  construction of Mathlib's `CategoryTheory.Functor.commShiftOfLocalization.iso`.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Complex

variable (n : ℕ) (K : CochainComplex C ℤ) [HasCompression n K] (k : ℤ)
  (hk : (k : ZMod n) = 0)

/-- The degreewise periodicity isomorphism `(Δₙ (K⟦k⟧))^r ≅ (Δₙ K)^r` for `k` divisible by `n`:
the summand of degree `i` of `K⟦k⟧` goes to the summand of degree `i + k` of `K` with the sign
`(-1)^(k * i)`. -/
noncomputable def compressionPeriodicityXIso (r : ZMod n) :
    (compression n (K⟦k⟧)).X r ≅ (compression n K).X r where
  hom := compressionDesc n (K⟦k⟧) fun i hi ↦
    (k * i).negOnePow • ((CochainComplex.shiftFunctorObjXIso K k i (i + k) rfl).hom ≫
      ιCompression n K (i + k) r (by simp [hi, hk]))
  inv := compressionDesc n K fun j hj ↦
    (k * (j - k)).negOnePow • ((CochainComplex.shiftFunctorObjXIso K k (j - k) j (by omega)).inv ≫
      ιCompression n (K⟦k⟧) (j - k) r (by simp [hj, hk]))
  hom_inv_id := by
    ext i hi
    dsimp
    simp only [ιCompression_compressionDesc_assoc, Linear.units_smul_comp,
      ιCompression_compressionDesc, smul_smul, add_sub_cancel_right,
      Int.units_mul_self, one_smul, Category.comp_id, Category.id_comp]
    exact XIsoOfEq_hom_comp_ιCompression (K := K⟦k⟧) n (Int.add_sub_cancel i k).symm r _
  inv_hom_id := by
    ext j hj
    dsimp
    simp only [ιCompression_compressionDesc_assoc, Linear.units_smul_comp, Category.assoc,
      ιCompression_compressionDesc, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
      one_smul, Category.comp_id, Category.id_comp]
    exact XIsoOfEq_hom_comp_ιCompression (K := K) n (Int.sub_add_cancel j k).symm r _

/-- On a summand, the periodicity isomorphism is the inclusion of the summand whose degree has
been translated by `k`, with the sign `(-1)^(k * i)`. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionPeriodicityXIso_hom (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) :
    ιCompression n (K⟦k⟧) i r hi ≫ (compressionPeriodicityXIso n K k hk r).hom =
      (k * i).negOnePow • ((CochainComplex.shiftFunctorObjXIso K k i (i + k) rfl).hom ≫
        ιCompression n K (i + k) r (by simp [hi, hk])) := by
  simp [compressionPeriodicityXIso]

/-- On a summand, the inverse periodicity isomorphism is the inclusion of the summand whose
degree has been translated back by `k`, with the sign `(-1)^(k * (j - k))`. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionPeriodicityXIso_inv (j : ℤ) (r : ZMod n) (hj : (j : ZMod n) = r) :
    ιCompression n K j r hj ≫ (compressionPeriodicityXIso n K k hk r).inv =
      (k * (j - k)).negOnePow •
        ((CochainComplex.shiftFunctorObjXIso K k (j - k) j (by omega)).inv ≫
          ιCompression n (K⟦k⟧) (j - k) r (by simp [hj, hk])) := by
  simp [compressionPeriodicityXIso]

/-- The compression of a complex is invariant under shifting it by a multiple `k` of `n`. The
isomorphism reindexes the summands by translation by `k` and multiplies the summand of degree
`i` by `(-1)^(k * i)`. -/
noncomputable def compressionPeriodicityIso : compression n (K⟦k⟧) ≅ compression n K :=
  HomologicalComplex.Hom.isoOfComponents (compressionPeriodicityXIso n K k hk) (fun r s hrs ↦ by
    ext i hi
    have hi₁ : ((i + 1 : ℤ) : ZMod n) = s := by
      rw [ComplexShape.up_Rel] at hrs
      simpa [← hi] using hrs
    rw [ιCompression_d_assoc n (K⟦k⟧) i (i + 1) rfl r s hi hi₁,
      ιCompression_compressionPeriodicityXIso_hom_assoc,
      ιCompression_compressionPeriodicityXIso_hom]
    simp only [CochainComplex.shiftFunctor_obj_d', CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul, Category.assoc]
    rw [ιCompression_d n K (i + k) (i + 1 + k) (by omega) r s (by simp [hi, hk])
      (by simp [hi₁, hk])]
    congr 1
    -- The signs agree: `(-1)^(k * (i + 1)) * (-1)^k = (-1)^(k * i)`.
    · rw [mul_add, mul_one, Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
    · simp)

/-- The component in residue degree `r` of the periodicity isomorphism. -/
@[simp]
lemma compressionPeriodicityIso_hom_f (r : ZMod n) :
    (compressionPeriodicityIso n K k hk).hom.f r = (compressionPeriodicityXIso n K k hk r).hom :=
  (rfl)

/-- The inverse component in residue degree `r` of the periodicity isomorphism. -/
@[simp]
lemma compressionPeriodicityIso_inv_f (r : ZMod n) :
    (compressionPeriodicityIso n K k hk).inv.f r = (compressionPeriodicityXIso n K k hk r).inv :=
  (rfl)

variable {K} in
/-- The periodicity isomorphism is natural in the complex. -/
@[reassoc]
lemma compressionPeriodicityIso_hom_naturality {L : CochainComplex C ℤ} [HasCompression n L]
    (f : K ⟶ L) :
    compressionMap n (f⟦k⟧') ≫ (compressionPeriodicityIso n L k hk).hom =
      (compressionPeriodicityIso n K k hk).hom ≫ compressionMap n f := by
  ext r i hi
  simp

/-- The periodicity isomorphisms for shifts by `a`, `b` and `c = a + b`, all divisible by `n`, are
compatible with the identification `K⟦c⟧ ≅ K⟦a⟧⟦b⟧` up to the sign `(-1)^(a * b)`. -/
@[reassoc]
lemma compressionPeriodicityIso_add_hom (a b c : ℤ) (h : a + b = c) (ha : (a : ZMod n) = 0)
    (hb : (b : ZMod n) = 0) (hc : (c : ZMod n) = 0) :
    compressionMap (L := K⟦a⟧⟦b⟧) n
        ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b c h).hom.app K) ≫
        (compressionPeriodicityIso n (K⟦a⟧) b hb).hom ≫ (compressionPeriodicityIso n K a ha).hom =
      (a * b).negOnePow • (compressionPeriodicityIso n K c hc).hom := by
  subst h
  ext r i hi
  -- The signs agree: `(-1)^(b * i) * (-1)^(a * (i + b)) = (-1)^(a * b) * (-1)^((a + b) * i)`.
  simp [CochainComplex.shiftFunctorAdd'_hom_app_f', smul_smul, ← Int.negOnePow_add,
    show b * i + a * (i + b) = a * b + (a + b) * i by ring]

section Bounded

variable [HasFiniteCoproducts C]

/-- The compression functor on bounded complexes is invariant under the shift by a multiple `k`
of `n`. -/
noncomputable def compressionFunctorPeriodicityIso :
    CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙ compressionFunctor n ≅
      compressionFunctor n :=
  shiftCompCompressionFunctorIso n k ≪≫
    NatIso.ofComponents (fun K ↦
      eqToIso (shiftCompressionFunctor_obj n k K) ≪≫ compressionPeriodicityIso n K.obj k hk ≪≫
        eqToIso (compressionFunctor_obj n K).symm)
      (fun {K L} f ↦ by
        simp [compressionPeriodicityIso_hom_naturality_assoc])

/-- The component of `compressionFunctorPeriodicityIso` at a bounded complex is the periodicity
isomorphism of its underlying complex, after identifying the underlying complex of its shift with
the shift of its underlying complex. -/
@[simp]
lemma compressionFunctorPeriodicityIso_hom_app (K : CochainComplex.Bounded C) :
    (compressionFunctorPeriodicityIso n k hk).hom.app K =
      eqToHom (compressionFunctor_obj n (K⟦k⟧)) ≫
        compressionMap (K := (K⟦k⟧).obj) (L := K.obj⟦k⟧) n
          (((CochainComplex.Bounded.ι C).commShiftIso k).hom.app K) ≫
          (compressionPeriodicityIso n K.obj k hk).hom ≫
            eqToHom (compressionFunctor_obj n K).symm := by
  simp only [compressionFunctorPeriodicityIso, Iso.trans_hom, NatTrans.comp_app,
    shiftCompCompressionFunctorIso_hom_app, NatIso.ofComponents_hom_app, eqToIso.hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The component of the inverse of `compressionFunctorPeriodicityIso` at a bounded complex is the
inverse periodicity isomorphism of its underlying complex, followed by the identification of the
shift of its underlying complex with the underlying complex of its shift. -/
@[simp]
lemma compressionFunctorPeriodicityIso_inv_app (K : CochainComplex.Bounded C) :
    (compressionFunctorPeriodicityIso n k hk).inv.app K =
      eqToHom (compressionFunctor_obj n K) ≫
        (compressionPeriodicityIso n K.obj k hk).inv ≫
          compressionMap (K := K.obj⟦k⟧) (L := (K⟦k⟧).obj) n
            (((CochainComplex.Bounded.ι C).commShiftIso k).inv.app K) ≫
            eqToHom (compressionFunctor_obj n (K⟦k⟧)).symm := by
  simp only [compressionFunctorPeriodicityIso, Iso.trans_inv, NatTrans.comp_app,
    shiftCompCompressionFunctorIso_inv_app, NatIso.ofComponents_inv_app, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The compression of a map `f : K ⟶ L⟦k⟧` of bounded complexes followed by the periodicity
isomorphism is, on the compressions of the underlying complexes, the compression of the underlying
chain map followed by the periodicity isomorphism of the underlying complex. -/
lemma compressionFunctor_map_comp_compressionFunctorPeriodicityIso_hom_app
    {K L : CochainComplex.Bounded C} (f : K ⟶ L⟦k⟧) :
    eqToHom (compressionFunctor_obj n K).symm ≫ (compressionFunctor n).map f ≫
        (compressionFunctorPeriodicityIso n k hk).hom.app L ≫
          eqToHom (compressionFunctor_obj n L) =
      compressionMap (L := L.obj⟦k⟧) n
          (f.hom ≫ ((CochainComplex.Bounded.ι C).commShiftIso k).hom.app L) ≫
        (compressionPeriodicityIso n L.obj k hk).hom := by
  simp [compressionMap_comp]

/-- The periodicity isomorphisms of compression of bounded complexes for shifts by `a`, `b` and
`c = a + b`, all divisible by `n`, compose to the one for `c` up to the sign `(-1)^(a * b)`. -/
lemma compressionFunctorPeriodicityIso_shiftComp_hom_app (a b c : ℤ) (h : a + b = c)
    (ha : (a : ZMod n) = 0) (hb : (b : ZMod n) = 0) (hc : (c : ZMod n) = 0)
    (K : CochainComplex.Bounded C) :
    ((compressionFunctorPeriodicityIso n a ha).shiftComp
        (compressionFunctorPeriodicityIso n b hb) h).hom.app K =
      (a * b).negOnePow • (compressionFunctorPeriodicityIso n c hc).hom.app K := by
  have h' : compressionMap (K := (K⟦c⟧).obj) (L := K.obj⟦a⟧⟦b⟧) n
      (((CategoryTheory.shiftFunctorAdd' _ a b c h).hom.app K).hom ≫
        ((CochainComplex.Bounded.ι C).commShiftIso b).hom.app (K⟦a⟧) ≫
          (((CochainComplex.Bounded.ι C).commShiftIso a).hom.app K)⟦b⟧') =
      compressionMap (K := (K⟦c⟧).obj) (L := K.obj⟦c⟧) n
          (((CochainComplex.Bounded.ι C).commShiftIso c).hom.app K) ≫
        compressionMap (K := K.obj⟦c⟧) (L := K.obj⟦a⟧⟦b⟧) n
          ((CategoryTheory.shiftFunctorAdd' _ a b c h).hom.app K.obj) := by
    rw [← compressionMap_comp]
    congr 1
    simp [Functor.commShiftIso_add' (CochainComplex.Bounded.ι C) h]
  simp only [Iso.shiftComp_hom_app, compressionFunctorPeriodicityIso_hom_app,
    compressionFunctor_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← compressionPeriodicityIso_hom_naturality_assoc, ← compressionMap_comp_assoc,
    ← compressionMap_comp_assoc, Category.assoc, h', Category.assoc,
    compressionPeriodicityIso_add_hom_assoc n K.obj a b c h ha hb hc]
  simp [Linear.comp_units_smul, Linear.units_smul_comp]

end Bounded

end Complex

section Homotopy

variable [HasFiniteCoproducts C] (n : ℕ) (k : ℤ) (hk : (k : ZMod n) = 0)

open HomotopyCategory.Bounded

/-- The compression functor `K^b(C) ⥤ K_n(C)` is invariant under the shift by a multiple `k` of
`n`. It is induced, along the localization functor `HomotopyCategory.Bounded.quotient C`, by the
periodicity isomorphism of compression of bounded complexes. -/
noncomputable def homotopyCompressionFunctorPeriodicityIso :
    CategoryTheory.shiftFunctor (HomotopyCategory.Bounded C) k ⋙ homotopyCompressionFunctor n ≅
      homotopyCompressionFunctor n :=
  have : HasBinaryBiproducts C := .of_hasBinaryCoproducts
  Localization.liftNatIso (quotient C)
    ((HomologicalComplex.homotopyEquivalences C (.up ℤ)).inverseImage
      (CochainComplex.Bounded.ι C))
    (quotient C ⋙ CategoryTheory.shiftFunctor _ k ⋙ homotopyCompressionFunctor n)
    (quotient C ⋙ homotopyCompressionFunctor n) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((quotient C).commShiftIso k).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (quotientCompHomotopyCompressionFunctorIso n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (compressionFunctorPeriodicityIso n k hk) _ ≪≫
      (quotientCompHomotopyCompressionFunctorIso n).symm)

/-- On the class of a bounded complex, the periodicity isomorphism of `K^b(C) ⥤ K_n(C)` is the
class of the periodicity isomorphism of compression, conjugated by the identifications of the
descended compression on classes of bounded complexes. -/
@[simp]
lemma homotopyCompressionFunctorPeriodicityIso_hom_app_quotient_obj
    (K : CochainComplex.Bounded C) :
    (homotopyCompressionFunctorPeriodicityIso n k hk).hom.app ((quotient C).obj K) =
      (homotopyCompressionFunctor n).map (((quotient C).commShiftIso k).inv.app K) ≫
        (quotientCompHomotopyCompressionFunctorIso n).hom.app (K⟦k⟧) ≫
          (HomotopyCategory.quotient C _).map
            ((compressionFunctorPeriodicityIso n k hk).hom.app K) ≫
            (quotientCompHomotopyCompressionFunctorIso n).inv.app K := by
  have : HasBinaryBiproducts C := .of_hasBinaryCoproducts
  simp [homotopyCompressionFunctorPeriodicityIso]

/-- On the class of a bounded complex, the inverse of the periodicity isomorphism of
`K^b(C) ⥤ K_n(C)` is the class of the inverse periodicity isomorphism of compression, conjugated by
the identifications of the descended compression on classes of bounded complexes. -/
@[simp]
lemma homotopyCompressionFunctorPeriodicityIso_inv_app_quotient_obj
    (K : CochainComplex.Bounded C) :
    (homotopyCompressionFunctorPeriodicityIso n k hk).inv.app ((quotient C).obj K) =
      (quotientCompHomotopyCompressionFunctorIso n).hom.app K ≫
        (HomotopyCategory.quotient C _).map
          ((compressionFunctorPeriodicityIso n k hk).inv.app K) ≫
          (quotientCompHomotopyCompressionFunctorIso n).inv.app (K⟦k⟧) ≫
            (homotopyCompressionFunctor n).map (((quotient C).commShiftIso k).hom.app K) := by
  have : HasBinaryBiproducts C := .of_hasBinaryCoproducts
  simp [homotopyCompressionFunctorPeriodicityIso]

/-- On the class of a bounded complex, the periodicity isomorphism of `K^b(C) ⥤ K_n(C)`, preceded
by the identification of the class of the shift with the shift of the class, is the class of the
periodicity isomorphism of compression, conjugated by the identifications of the descended
compression on classes of bounded complexes. -/
@[reassoc]
lemma map_commShiftIso_hom_app_comp_homotopyCompressionFunctorPeriodicityIso_hom_app
    (K : CochainComplex.Bounded C) :
    (homotopyCompressionFunctor n).map (((quotient C).commShiftIso k).hom.app K) ≫
        (homotopyCompressionFunctorPeriodicityIso n k hk).hom.app ((quotient C).obj K) =
      (quotientCompHomotopyCompressionFunctorIso n).hom.app (K⟦k⟧) ≫
        (HomotopyCategory.quotient C _).map
          ((compressionFunctorPeriodicityIso n k hk).hom.app K) ≫
          (quotientCompHomotopyCompressionFunctorIso n).inv.app K := by
  rw [homotopyCompressionFunctorPeriodicityIso_hom_app_quotient_obj, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The periodicity isomorphisms of `K^b(C) ⥤ K_n(C)` for shifts by `a`, `b` and `c = a + b`, all
divisible by `n`, compose to the one for `c` up to the sign `(-1)^(a * b)`. -/
lemma homotopyCompressionFunctorPeriodicityIso_shiftComp_hom_app (a b c : ℤ) (h : a + b = c)
    (ha : (a : ZMod n) = 0) (hb : (b : ZMod n) = 0) (hc : (c : ZMod n) = 0)
    (X : HomotopyCategory.Bounded C) :
    ((homotopyCompressionFunctorPeriodicityIso n a ha).shiftComp
        (homotopyCompressionFunctorPeriodicityIso n b hb) h).hom.app X =
      (a * b).negOnePow • (homotopyCompressionFunctorPeriodicityIso n c hc).hom.app X := by
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X
  rw [← cancel_epi ((homotopyCompressionFunctor n).map (((quotient C).commShiftIso c).hom.app K)),
    Linear.comp_units_smul,
    map_commShiftIso_hom_app_comp_homotopyCompressionFunctorPeriodicityIso_hom_app,
    Iso.shiftComp_hom_app]
  have hσ : ((quotient C).commShiftIso c).hom.app K ≫
      (CategoryTheory.shiftFunctorAdd' _ a b c h).hom.app ((quotient C).obj K) =
        (quotient C).map ((CategoryTheory.shiftFunctorAdd' _ a b c h).hom.app K) ≫
          ((quotient C).commShiftIso b).hom.app (K⟦a⟧) ≫
            (((quotient C).commShiftIso a).hom.app K)⟦b⟧' := by
    simp [Functor.commShiftIso_add' (quotient C) h]
  have hnat := (homotopyCompressionFunctorPeriodicityIso n b hb).hom.naturality
    (((quotient C).commShiftIso a).hom.app K)
  simp only [Functor.comp_map] at hnat
  rw [← Functor.map_comp_assoc, hσ, Functor.map_comp_assoc, Functor.map_comp_assoc,
    reassoc_of% hnat,
    map_commShiftIso_hom_app_comp_homotopyCompressionFunctorPeriodicityIso_hom_app_assoc,
    map_commShiftIso_hom_app_comp_homotopyCompressionFunctorPeriodicityIso_hom_app,
    Iso.inv_hom_id_app_assoc]
  have hE := (quotientCompHomotopyCompressionFunctorIso n).hom.naturality
    ((CategoryTheory.shiftFunctorAdd' _ a b c h).hom.app K)
  simp only [Functor.comp_map] at hE
  rw [reassoc_of% hE, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    ← Iso.shiftComp_hom_app, compressionFunctorPeriodicityIso_shiftComp_hom_app n a b c h ha hb hc]
  simp [Units.smul_def]

/-- The periodicity isomorphism of `K^b(C) ⥤ K_n(C)` for the shift by `k = 0` is induced by the
identification `X⟦0⟧ ≅ X`. -/
lemma homotopyCompressionFunctorPeriodicityIso_eq_of_eq_zero (h : k = 0) :
    homotopyCompressionFunctorPeriodicityIso n k hk =
      Functor.isoWhiskerRight (CategoryTheory.shiftFunctorZero' _ k h)
        (homotopyCompressionFunctor (C := C) n) ≪≫
        (homotopyCompressionFunctor n).leftUnitor := by
  rw [← Iso.shiftComp_left_cancel_iff (homotopyCompressionFunctorPeriodicityIso n k hk)
    (show k + k = k by omega), Iso.shiftComp_zero_right]
  ext X
  rw [homotopyCompressionFunctorPeriodicityIso_shiftComp_hom_app n k k k _ hk hk hk,
    show (k * k).negOnePow = 1 by simp [h], one_smul]

/-- The orbit functor `K^b(C)/[n] ⥤ K_n(C)`: the descent of the compression functor
`K^b(C) ⥤ K_n(C)` to the orbit category, along its periodicity isomorphism for the shift by `n`.
It restricts to compression along the projection `K^b(C) ⥤ K^b(C)/[n]`
(`TauCeti.OrbitCategory.projectionCompLift`). -/
noncomputable abbrev orbitCompressionFunctor :
    OrbitCategory (HomotopyCategory.Bounded C) n ⥤ HomotopyCategory C (.up (ZMod n)) :=
  OrbitCategory.lift (homotopyCompressionFunctor n)
    (homotopyCompressionFunctorPeriodicityIso n n (by simp))

end Homotopy

end TauCeti.PeriodicComplex
