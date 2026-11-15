/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.Algebra.Homology.Periodic.Compression.Shift
public import TauCeti.Algebra.Homology.Periodic.Triangulated

/-!
# Compression of mapping cones

The `n`-periodic compression `Δₙ` of the mapping cone of a morphism `φ : K ⟶ L` of
integer-indexed cochain complexes is the periodic mapping cone of `Δₙ φ`. In residue degree `r`,
the summand `K^(i+1) ⊞ L^i` of `Δₙ (cone φ)`, for `i ≡ r` modulo `n`, goes to the summands of
degrees `i + 1` and `i` of `(Δₙ K)^(r+1) ⊞ (Δₙ L)^r`. No signs are introduced: the cone
differentials on both sides are `[[-d, 0], [φ, d]]`.

The comparison is `TauCeti.PeriodicComplex.compressionMappingConeIso`. Its inverse is the morphism
out of the periodic cone determined by the compression of `inr φ` and the compression of the
standard null-homotopy of `φ ≫ inr φ`. Together with the comparison
`TauCeti.PeriodicComplex.compressionShiftIso` of compression with the shift, it identifies the
compression of Mathlib's mapping-cone triangle `CochainComplex.mappingCone.triangle φ` with the
periodic mapping-cone triangle of `Δₙ φ`
(`TauCeti.PeriodicComplex.compressionMappingConeTriangleIso`). Consequently the image of the
compressed triangle in the periodic homotopy category is distinguished
(`TauCeti.PeriodicComplex.compressionMappingConeTriangle_mem_distTriang`).

The results hold for every morphism between complexes whose compressions exist, for instance
bounded complexes: the degree-`r` term of the periodic cone exhibits the required coproduct for
the mapping cone (`TauCeti.PeriodicComplex.hasCompression_mappingCone`).

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

open CategoryTheory Limits Pretriangulated HomologicalComplex

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C] (n : ℕ)
  {K L : CochainComplex C ℤ} (φ : K ⟶ L) [HasCompression n K] [HasCompression n L]

open CochainComplex

/-- The inclusion of the summand `K^(i+1) ⊞ L^i` of the mapping cone into the degree-`r` term of
the periodic mapping cone of the compressed map, for `i ≡ r`. -/
private noncomputable def coneInj (r : ZMod n) (i : ℤ) (hi : (i : ZMod n) = r) :
    (mappingCone φ).X i ⟶ (homotopyCofiber (compressionMap n φ)).X r :=
  (mappingCone.fst φ).1.v i (i + 1) rfl ≫ ιCompression n K (i + 1) (r + 1) (by simp [hi]) ≫
      homotopyCofiber.inlX (compressionMap n φ) (r + 1) r (by simp) +
    (mappingCone.snd φ).v i i (add_zero i) ≫ ιCompression n L i r hi ≫
      homotopyCofiber.inrX (compressionMap n φ) r

private lemma coneInj_eq (i j : ℤ) (hij : i + 1 = j) (r s : ZMod n)
    (hi : (i : ZMod n) = r) (hs : (ComplexShape.up (ZMod n)).Rel r s) :
    coneInj n φ r i hi =
      (mappingCone.fst φ).1.v i j hij ≫ ιCompression n K j s (by
        rw [ComplexShape.up_Rel] at hs; simp [← hs, ← hij, hi]) ≫
          homotopyCofiber.inlX (compressionMap n φ) s r hs +
        (mappingCone.snd φ).v i i (add_zero i) ≫ ιCompression n L i r hi ≫
          homotopyCofiber.inrX (compressionMap n φ) r := by
  subst hij
  have hs' : r + 1 = s := hs
  subst hs'
  rfl

@[reassoc]
private lemma inl_v_coneInj (i j : ℤ) (hij : i + 1 = j) (r s : ZMod n)
    (hi : (i : ZMod n) = r) (hs : (ComplexShape.up (ZMod n)).Rel r s) :
    (mappingCone.inl φ).v j i (by omega) ≫ coneInj n φ r i hi =
      ιCompression n K j s (by rw [ComplexShape.up_Rel] at hs; simp [← hs, ← hij, hi]) ≫
        homotopyCofiber.inlX (compressionMap n φ) s r hs := by
  simp [coneInj_eq n φ i j hij r s hi hs]

@[reassoc]
private lemma inr_f_coneInj (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) :
    (mappingCone.inr φ).f i ≫ coneInj n φ r i hi =
      ιCompression n L i r hi ≫ homotopyCofiber.inrX (compressionMap n φ) r := by
  simp [coneInj]

/-- The morphism out of the degree-`r` term of the periodic mapping cone of the compressed map
induced by a family of morphisms out of the terms `(mappingCone φ).X i` with `i ≡ r`. -/
private noncomputable def coneDesc (r : ZMod n) {A : C}
    (f : ∀ (i : ℤ) (_ : (i : ZMod n) = r), (mappingCone φ).X i ⟶ A) :
    (homotopyCofiber (compressionMap n φ)).X r ⟶ A :=
  homotopyCofiber.fstX (compressionMap n φ) r (r + 1) (by simp) ≫
      compressionDesc n K (fun j hj ↦ (mappingCone.inl φ).v j (j - 1) (by omega) ≫
        f (j - 1) (by simp [hj])) +
    homotopyCofiber.sndX (compressionMap n φ) r ≫
      compressionDesc n L (fun i hi ↦ (mappingCone.inr φ).f i ≫ f i hi)

omit [HasCompression n K] [HasCompression n L] in
private lemma inl_v_comp_congr (j a b : ℤ) (hab : a = b) (r : ZMod n) {A : C}
    (f : ∀ (i : ℤ) (_ : (i : ZMod n) = r), (mappingCone φ).X i ⟶ A)
    (ha : j + -1 = a) (ha' : (a : ZMod n) = r) :
    (mappingCone.inl φ).v j a ha ≫ f a ha' =
      (mappingCone.inl φ).v j b (by omega) ≫ f b (by rwa [← hab]) := by
  subst hab
  rfl

@[reassoc]
private lemma ιCompression_inlX_coneDesc (i j : ℤ) (hij : i + 1 = j) (r s : ZMod n)
    (hi : (i : ZMod n) = r) (hs : (ComplexShape.up (ZMod n)).Rel r s) {A : C}
    (f : ∀ (i : ℤ) (_ : (i : ZMod n) = r), (mappingCone φ).X i ⟶ A) :
    ιCompression n K j s (by rw [ComplexShape.up_Rel] at hs; simp [← hs, ← hij, hi]) ≫
        homotopyCofiber.inlX (compressionMap n φ) s r hs ≫ coneDesc n φ r f =
      (mappingCone.inl φ).v j i (by omega) ≫ f i hi := by
  have hs' : r + 1 = s := hs
  subst hs'
  simp [coneDesc, inl_v_comp_congr n φ j (j - 1) i (by omega) r f]

@[reassoc]
private lemma ιCompression_inrX_coneDesc (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) {A : C}
    (f : ∀ (i : ℤ) (_ : (i : ZMod n) = r), (mappingCone φ).X i ⟶ A) :
    ιCompression n L i r hi ≫ homotopyCofiber.inrX (compressionMap n φ) r ≫ coneDesc n φ r f =
      (mappingCone.inr φ).f i ≫ f i hi := by
  simp [coneDesc]

/-- The degree-`r` term of the periodic mapping cone of the compressed map is a coproduct of the
terms of the mapping cone in the degrees congruent to `r`. -/
private noncomputable def isColimitConeCofan (r : ZMod n) :
    IsColimit (Cofan.mk (f := GradedObject.mapObjFun (mappingCone φ).X (fun i : ℤ ↦ (i : ZMod n)) r)
      ((homotopyCofiber (compressionMap n φ)).X r) fun i ↦
        coneInj n φ r i.1 (Set.mem_singleton_iff.mp (Set.mem_preimage.mp i.2))) :=
  Cofan.IsColimit.mk _
    (fun t ↦ coneDesc n φ r fun i hi ↦
      t.inj ⟨i, Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hi)⟩)
    (fun t ⟨i, hi⟩ ↦ by
      have hi' : (i : ZMod n) = r := hi
      rw [cofan_mk_inj]
      apply mappingCone.ext_from φ (i + 1) i rfl
      · rw [inl_v_coneInj_assoc n φ i (i + 1) rfl r (r + 1) hi' (by simp),
          ιCompression_inlX_coneDesc n φ i (i + 1) rfl r (r + 1) hi' (by simp)]
      · rw [inr_f_coneInj_assoc n φ i r hi', ιCompression_inrX_coneDesc n φ i r hi'])
    (fun t m hm ↦ by
      apply homotopyCofiber.ext_from_X (compressionMap n φ) (r + 1) r (by simp)
      · ext j hj
        have hi : ((j - 1 : ℤ) : ZMod n) = r := by simp [hj]
        rw [ιCompression_inlX_coneDesc n φ (j - 1) j (by omega) r (r + 1) hi (by simp),
          ← hm ⟨j - 1, Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hi)⟩, cofan_mk_inj,
          inl_v_coneInj_assoc n φ (j - 1) j (by omega) r (r + 1) hi (by simp)]
      · ext i hi
        rw [ιCompression_inrX_coneDesc n φ i r hi,
          ← hm ⟨i, Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hi)⟩, cofan_mk_inj,
          inr_f_coneInj_assoc n φ i r hi])

/-- The mapping cone of a morphism of complexes with `n`-periodic compressions has an `n`-periodic
compression: in each residue class, the coproduct is the corresponding term of the periodic
mapping cone of the compressed map. -/
instance hasCompression_mappingCone : HasCompression n (mappingCone φ) := fun r ↦
  ⟨⟨⟨_, isColimitConeCofan n φ r⟩⟩⟩

/-- The compression of `φ ≫ inr φ` is null-homotopic, by the compression of the standard
null-homotopy of `φ ≫ inr φ`. -/
noncomputable def compressionMappingConeInrHomotopy :
    Homotopy (compressionMap n φ ≫ compressionMap n (mappingCone.inr φ)) 0 :=
  (Homotopy.ofEq (compressionMap_comp n _ _).symm).trans
    ((compressionHomotopy n (mappingCone.inrCompHomotopy φ)).trans
      (Homotopy.ofEq (compressionMap_zero n _ _)))

@[reassoc]
lemma ιCompression_compressionMappingConeInrHomotopy_hom (i j : ℤ) (hij : j + 1 = i)
    (r s : ZMod n) (hi : (i : ZMod n) = r) (hj : (j : ZMod n) = s) :
    ιCompression n K i r hi ≫ (compressionMappingConeInrHomotopy n φ).hom r s =
      (mappingCone.inl φ).v i j (by omega) ≫ ιCompression n (mappingCone φ) j s hj := by
  simp only [compressionMappingConeInrHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Pi.zero_apply, zero_add, add_zero]
  rw [ιCompression_compressionHomotopy_hom n (mappingCone.inrCompHomotopy φ)
      i j hij r s hi hj,
    mappingCone.inrCompHomotopy_hom φ i j hij]

/-- The comparison from the periodic mapping cone of the compressed map to the compression of the
mapping cone. It is induced by the compressed inclusion `inr φ` and the compressed null-homotopy
of `φ ≫ inr φ`. -/
private noncomputable def coneToCompression :
    homotopyCofiber (compressionMap n φ) ⟶ compression n (mappingCone φ) :=
  homotopyCofiber.desc _ (compressionMap n (mappingCone.inr φ))
    (compressionMappingConeInrHomotopy n φ)

@[reassoc]
private lemma inlX_coneToCompression_f (r s : ZMod n)
    (hrs : (ComplexShape.up (ZMod n)).Rel r s) :
    homotopyCofiber.inlX (compressionMap n φ) s r hrs ≫ (coneToCompression n φ).f r =
      (compressionMappingConeInrHomotopy n φ).hom s r :=
  homotopyCofiber.inlX_desc_f _ _ _ s r hrs

@[reassoc]
private lemma inrX_coneToCompression_f (r : ZMod n) :
    homotopyCofiber.inrX (compressionMap n φ) r ≫ (coneToCompression n φ).f r =
      (compressionMap n (mappingCone.inr φ)).f r :=
  homotopyCofiber.inrX_desc_f _ _ _ r

/-- The degreewise inverse of `coneToCompression`, defined summand by summand. -/
private noncomputable def compressionToConeX (r : ZMod n) :
    (compression n (mappingCone φ)).X r ⟶ (homotopyCofiber (compressionMap n φ)).X r :=
  compressionDesc n (mappingCone φ) (coneInj n φ r)

@[reassoc]
private lemma ιCompression_compressionToConeX (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) :
    ιCompression n (mappingCone φ) i r hi ≫ compressionToConeX n φ r = coneInj n φ r i hi := by
  simp [compressionToConeX]

/-- The compression of the mapping cone is degreewise isomorphic to the periodic mapping cone of
the compressed map. -/
private noncomputable def coneToCompressionXIso (r : ZMod n) :
    (homotopyCofiber (compressionMap n φ)).X r ≅ (compression n (mappingCone φ)).X r where
  hom := (coneToCompression n φ).f r
  inv := compressionToConeX n φ r
  hom_inv_id := by
    apply homotopyCofiber.ext_from_X (compressionMap n φ) (r + 1) r (by simp)
    · ext j hj
      have hi : ((j - 1 : ℤ) : ZMod n) = r := by simp [hj]
      simp [inlX_coneToCompression_f_assoc,
        ιCompression_compressionMappingConeInrHomotopy_hom_assoc n φ j (j - 1) (by omega)
          (r + 1) r hj hi, ιCompression_compressionToConeX,
        inl_v_coneInj n φ (j - 1) j (by omega) r (r + 1) hi (by simp)]
    · ext i hi
      simp [inrX_coneToCompression_f_assoc, ιCompression_compressionToConeX, inr_f_coneInj]
  inv_hom_id := by
    ext i hi
    apply mappingCone.ext_from φ (i + 1) i rfl
    · simp [ιCompression_compressionToConeX_assoc,
        inl_v_coneInj_assoc n φ i (i + 1) rfl r (r + 1) hi (by simp), inlX_coneToCompression_f,
        ιCompression_compressionMappingConeInrHomotopy_hom n φ (i + 1) i rfl (r + 1) r
          (by simp [hi]) hi]
    · simp [ιCompression_compressionToConeX_assoc, inr_f_coneInj_assoc,
        inrX_coneToCompression_f]

/-- **Compression of mapping cones.** The compression of the mapping cone of `φ` is isomorphic to
the periodic mapping cone of the compression of `φ`. In residue degree `r`, the summand
`K^(i+1) ⊞ L^i` of the left side, for `i ≡ r`, is sent to the summands of degrees `i + 1` and `i`
of `(Δₙ K)^(r+1) ⊞ (Δₙ L)^r`. -/
noncomputable def compressionMappingConeIso :
    compression n (mappingCone φ) ≅ homotopyCofiber (compressionMap n φ) :=
  (Hom.isoOfComponents (coneToCompressionXIso n φ)
    (fun r s _ ↦ (coneToCompression n φ).comm r s)).symm

/-- The inverse comparison is the morphism out of the periodic cone determined by the compression
of `inr φ` and the compressed null-homotopy of `φ ≫ inr φ`. -/
lemma compressionMappingConeIso_inv :
    (compressionMappingConeIso n φ).inv =
      homotopyCofiber.desc _ (compressionMap n (mappingCone.inr φ))
        (compressionMappingConeInrHomotopy n φ) := by
  ext r
  rfl

/-- On the summand of degree `i`, the comparison is given by the two projections of the mapping
cone followed by the inclusions into the compressions. -/
@[reassoc]
lemma ιCompression_compressionMappingConeIso_hom_f (i j : ℤ) (hij : i + 1 = j) (r s : ZMod n)
    (hi : (i : ZMod n) = r) (hs : (ComplexShape.up (ZMod n)).Rel r s) :
    ιCompression n (mappingCone φ) i r hi ≫ (compressionMappingConeIso n φ).hom.f r =
      (mappingCone.fst φ).1.v i j hij ≫ ιCompression n K j s (by
        rw [ComplexShape.up_Rel] at hs; simp [← hs, ← hij, hi]) ≫
          homotopyCofiber.inlX (compressionMap n φ) s r hs +
        (mappingCone.snd φ).v i i (add_zero i) ≫ ιCompression n L i r hi ≫
          homotopyCofiber.inrX (compressionMap n φ) r :=
  (ιCompression_compressionToConeX n φ i r hi).trans (coneInj_eq n φ i j hij r s hi hs)

/-- On the left summand of the periodic cone, the inverse comparison is the compression of the
left inclusion `inl φ` of the mapping cone. -/
@[reassoc]
lemma ιCompression_inlX_compressionMappingConeIso_inv_f (i j : ℤ) (hij : i + 1 = j)
    (r s : ZMod n) (hi : (i : ZMod n) = r) (hs : (ComplexShape.up (ZMod n)).Rel r s) :
    ιCompression n K j s (by
        rw [ComplexShape.up_Rel] at hs; simp [← hs, ← hij, hi]) ≫
        homotopyCofiber.inlX (compressionMap n φ) s r hs ≫
          (compressionMappingConeIso n φ).inv.f r =
      (mappingCone.inl φ).v j i (by omega) ≫ ιCompression n (mappingCone φ) i r hi :=
  (congrArg (ιCompression n K j s _ ≫ ·) (inlX_coneToCompression_f n φ r s hs)).trans
    (ιCompression_compressionMappingConeInrHomotopy_hom n φ j i hij s r _ hi)

/-- On the right summand of the periodic cone, the inverse comparison is the compression of the
right inclusion `inr φ` of the mapping cone. -/
@[reassoc (attr := simp)]
lemma ιCompression_inrX_compressionMappingConeIso_inv_f (i : ℤ) (r : ZMod n)
    (hi : (i : ZMod n) = r) :
    ιCompression n L i r hi ≫ homotopyCofiber.inrX (compressionMap n φ) r ≫
        (compressionMappingConeIso n φ).inv.f r =
      (mappingCone.inr φ).f i ≫ ιCompression n (mappingCone φ) i r hi := by
  rw [compressionMappingConeIso_inv, homotopyCofiber.inrX_desc_f,
    ιCompression_compressionMap_f]

/-- The right inclusion of the periodic cone followed by the inverse comparison is the
compression of `inr φ`. -/
@[reassoc (attr := simp)]
lemma inr_comp_compressionMappingConeIso_inv :
    homotopyCofiber.inr (compressionMap n φ) ≫ (compressionMappingConeIso n φ).inv =
      compressionMap n (mappingCone.inr φ) := by
  rw [compressionMappingConeIso_inv, homotopyCofiber.inr_desc]

/-- The compression of the inclusion `inr φ` corresponds to the inclusion of the periodic
cone. -/
@[reassoc (attr := simp)]
lemma compressionMap_inr_comp_compressionMappingConeIso_hom :
    compressionMap n (mappingCone.inr φ) ≫ (compressionMappingConeIso n φ).hom =
      homotopyCofiber.inr (compressionMap n φ) := by
  rw [← Iso.eq_comp_inv, compressionMappingConeIso_inv, homotopyCofiber.inr_desc]

@[reassoc]
private lemma ιCompression_inlX_fstX (j : ℤ) (r s t : ZMod n)
    (hs : (ComplexShape.up (ZMod n)).Rel r s) (ht : (ComplexShape.up (ZMod n)).Rel r t)
    (hj : (j : ZMod n) = s) :
    ιCompression n K j s hj ≫ homotopyCofiber.inlX (compressionMap n φ) s r hs ≫
        homotopyCofiber.fstX (compressionMap n φ) r t ht =
      ιCompression n K j t (by
        rw [ComplexShape.up_Rel] at hs ht
        rw [hj, ← hs, ht]) := by
  have hs' : r + 1 = s := hs
  have ht' : r + 1 = t := ht
  subst hs' ht'
  simp

/-- The compression of the third morphism of the mapping-cone triangle of `φ`, followed by the
comparison of compression with the shift, corresponds to minus the projection of the periodic
cone. -/
@[reassoc]
lemma compressionMappingConeIso_hom_comp_coneProjection :
    (compressionMappingConeIso n φ).hom ≫ coneProjection (compressionMap n φ) =
      -(compressionMap n
          (HomComplex.Cocycle.homOf ((-mappingCone.fst φ).rightShift 1 0 (zero_add 1))) ≫
        (compressionShiftIso n K 1).hom) := by
  ext r i hi
  -- Mathlib's formulas for the third morphism of `mappingCone.triangle φ`, stated for the
  -- underlying morphism `Cocycle.homOf _` appearing in the goal.
  have h₁ : (mappingCone.inl φ).v (i + 1) i (by omega) ≫
      (HomComplex.Cocycle.homOf ((-mappingCone.fst φ).rightShift 1 0 (zero_add 1))).f i =
        -(K.shiftFunctorObjXIso 1 i (i + 1) rfl).inv :=
    mappingCone.inl_v_triangle_mor₃_f φ (i + 1) i (by omega)
  have h₂ : (mappingCone.inr φ).f i ≫
      (HomComplex.Cocycle.homOf ((-mappingCone.fst φ).rightShift 1 0 (zero_add 1))).f i = 0 :=
    mappingCone.inr_f_triangle_mor₃_f φ i
  apply mappingCone.ext_from φ (i + 1) i rfl
  · simp [-HomComplex.Cocycle.homOf_f,
      ιCompression_compressionMappingConeIso_hom_f_assoc n φ i (i + 1) rfl r (r + 1) hi (by simp),
      ιCompression_inlX_fstX n φ (i + 1) r (r + 1) (r + ((1 : ℤ) : ZMod n)) (by simp) (by simp),
      reassoc_of% h₁,
      CochainComplex.shiftFunctorObjXIso]
  · simp [-HomComplex.Cocycle.homOf_f,
      ιCompression_compressionMappingConeIso_hom_f_assoc n φ i (i + 1) rfl r (r + 1) hi (by simp),
      reassoc_of% h₂]

/-- The compression of the mapping-cone triangle `K ⟶ L ⟶ mappingCone φ ⟶ K⟦1⟧` of `φ`: its
morphisms are the compressions of `φ`, of `inr φ` and of the third morphism of
`mappingCone.triangle φ` (the morphism induced by the cocycle `-fst φ`), the last followed by the
comparison `compressionShiftIso` of compression with the shift. -/
-- The morphisms are typed by the vertices, so the vertices must compute for consumers.
@[expose, implicit_reducible, simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
noncomputable def compressionMappingConeTriangle : Triangle (CochainComplex C (ZMod n)) :=
  Triangle.mk (compressionMap n φ) (compressionMap n (mappingCone.inr φ))
    (compressionMap n
        (HomComplex.Cocycle.homOf ((-mappingCone.fst φ).rightShift 1 0 (zero_add 1))) ≫
      (compressionShiftIso n K 1).hom)

/-- **Compression preserves mapping-cone triangles.** The compression of the mapping-cone triangle
of `φ` is isomorphic to the periodic mapping-cone triangle of the compression of `φ`, by the
identity on the first two vertices and `compressionMappingConeIso` on the cone. -/
noncomputable def compressionMappingConeTriangleIso :
    compressionMappingConeTriangle n φ ≅
      Triangle.mk (compressionMap n φ) (homotopyCofiber.inr (compressionMap n φ))
        (-coneProjection (compressionMap n φ)) :=
  Triangle.isoMk _ _ (Iso.refl (compression n K)) (Iso.refl (compression n L))
    (compressionMappingConeIso n φ) (by simp) (by simp)
    (by simp [compressionMappingConeIso_hom_comp_coneProjection])

/-- The image in the periodic homotopy category of the compression of the mapping-cone triangle of
a morphism of cochain complexes is distinguished. -/
theorem compressionMappingConeTriangle_mem_distTriang [HasZeroObject C] :
    (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).mapTriangle.obj
        (compressionMappingConeTriangle n φ) ∈
      distTriang (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  isomorphic_distinguished _ (mappingCone_mem_distTriang (compressionMap n φ)) _
    ((HomotopyCategory.quotient C _).mapTriangle.mapIso (compressionMappingConeTriangleIso n φ))

end TauCeti.PeriodicComplex
