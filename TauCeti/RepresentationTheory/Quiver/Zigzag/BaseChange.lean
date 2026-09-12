/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BaseChange
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew

/-!
# Scalar extension of skew-zigzag relation quotients

A homomorphism of coefficient rings sends every unit-valued ratio of a skew-zigzag parameter to
a unit-valued ratio over the target.  The resulting parameter has a canonical coefficient map

```text
Z_k(G,c) → Z_l(G,c.map f)
```

which fixes the doubled paths and applies `f : k →+* l` to their coefficients.  This is the
presentation-level scalar-extension map; it does not identify the target with a tensor product.
The parameter construction is functorial in the coefficient homomorphism.

The parameter construction only needs a monoid homomorphism.  Injectivity is stated exactly when
the induced map on units is injective, since the parameters only record unit-valued ratios.

## Main definitions

* `TauCeti.skewZigzagBaseChange`: the induced coefficient map between relation quotients.

## Main results

* `TauCeti.skewZigzagBaseChange_skewZigzagMk_ofPath`: scalar extension fixes every doubled path.
* `TauCeti.skewZigzagBaseChange_algebraMap`: scalar coefficients are transported by the given
  ring homomorphism.
* `TauCeti.skewZigzagBaseChange_id` and `TauCeti.skewZigzagBaseChange_comp`: scalar extension is
  functorial in the coefficient homomorphism.

The parameter conventions follow C. Couture, *Skew-Zigzag Algebras*, Sections 3 and 4,
https://arxiv.org/abs/1509.08405.  The coefficient-map construction follows
`TauCeti.RepresentationTheory.Quiver.Preprojective.BaseChange`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u w z

section Quotient

variable {k : Type w} {l : Type z} {V : Type u}
  [CommRing k] [CommRing l] (G : SimpleGraph V) [Finite V]

private noncomputable def skewZigzagBaseChangePathAlgHom
    (f : k →+* l) (c : SkewZigzagParameter k G) :
    letI : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
        (fun a x => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) x)
    pathAlgebra k (DoubledQuiver G) →ₐ[k] skewZigzagQuotient l G (c.map (f : k →* l)) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
      (fun a x => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) x)
  exact PathAlgebra.baseChangeAlgHom f (skewZigzagMk l G (c.map (f : k →* l)))

private theorem skewZigzagBaseChangePathAlgHom_ofPath
    (f : k →+* l) (c : SkewZigzagParameter k G)
    (x : Quiver.TotalPath (DoubledQuiver G)) :
    letI : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
        (fun a y => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
    skewZigzagBaseChangePathAlgHom G f c (ofPath x) =
      skewZigzagMk l G (c.map (f : k →* l)) (ofPath x) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
  exact PathAlgebra.baseChangeAlgHom_ofPath f
    (skewZigzagMk l G (c.map (f : k →* l))) x

private theorem skewZigzagBaseChangePathAlgHom_relator
    (f : k →+* l) (c : SkewZigzagParameter k G)
    (x : pathAlgebra k (DoubledQuiver G)) (hx : IsSkewZigzagRelator k G c x) :
    letI : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
        (fun a y => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
    skewZigzagBaseChangePathAlgHom G f c x = 0 := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
  cases hx with
  | nonreturn p hlen hne =>
      rw [skewZigzagBaseChangePathAlgHom_ofPath]
      exact skewZigzagMk_ofPath_eq_zero_of_ne l G (c.map (f : k →* l)) p hlen hne
  | backtrack_ratio h h' =>
      rw [map_sub, map_smul, sub_eq_zero]
      calc
        skewZigzagBaseChangePathAlgHom G f c (backtrackElem G k h) =
            skewZigzagMk l G (c.map (f : k →* l)) (backtrackElem G l h) := by
          rw [backtrackElem_eq_ofPath, skewZigzagBaseChangePathAlgHom_ofPath,
            backtrackElem_eq_ofPath]
        _ =
            ((c.map (f : k →* l)).ratio h h' : l) •
              skewZigzagMk l G (c.map (f : k →* l)) (backtrackElem G l h') :=
          skewZigzagMk_backtrackElem_eq_smul l G (c.map (f : k →* l)) h h'
        _ = (c.ratio h h' : k) •
              skewZigzagMk l G (c.map (f : k →* l)) (backtrackElem G l h') := by
          rw [RingHom.smul_toAlgebra', RingHom.comp_apply]
          simp only [SkewZigzagParameter.map_ratio, Units.coe_map, MonoidHom.coe_coe]
          rw [Algebra.smul_def]
        _ = (c.ratio h h' : k) •
              skewZigzagBaseChangePathAlgHom G f c (backtrackElem G k h') := by
          congr 1
          symm
          rw [backtrackElem_eq_ofPath, skewZigzagBaseChangePathAlgHom_ofPath,
            backtrackElem_eq_ofPath]
  | long_path y h3 =>
      rw [skewZigzagBaseChangePathAlgHom_ofPath]
      exact skewZigzagMk_ofPath_eq_zero_of_three_le l G (c.map (f : k →* l)) y h3

private noncomputable def skewZigzagBaseChangeAlgHom
    (f : k →+* l) (c : SkewZigzagParameter k G) :
    letI : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
        (fun a y => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
    skewZigzagQuotient k G c →ₐ[k] skewZigzagQuotient l G (c.map (f : k →* l)) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
  exact skewZigzagLift k G c (skewZigzagBaseChangePathAlgHom G f c)
    (skewZigzagBaseChangePathAlgHom_relator G f c)

/-- The coefficient map on a skew-zigzag relation quotient.

It fixes every doubled path and applies `f` to scalar coefficients.  The codomain carries the
parameter obtained by applying `f` to every unit-valued ratio. -/
noncomputable def skewZigzagBaseChange (f : k →+* l) (c : SkewZigzagParameter k G) :
    skewZigzagQuotient k G c →+* skewZigzagQuotient l G (c.map (f : k →* l)) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
  exact (skewZigzagBaseChangeAlgHom G f c).toRingHom

/-- Scalar extension sends the class of every doubled path to the class of the same path over the
target coefficient ring. -/
@[simp]
theorem skewZigzagBaseChange_skewZigzagMk_ofPath
    (f : k →+* l) (c : SkewZigzagParameter k G)
    (x : Quiver.TotalPath (DoubledQuiver G)) :
    skewZigzagBaseChange G f c (skewZigzagMk k G c (ofPath x)) =
      skewZigzagMk l G (c.map (f : k →* l)) (ofPath x) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f a) y)
  -- The public map is the underlying ring map of the quotient lift.
  change skewZigzagBaseChangeAlgHom G f c (skewZigzagMk k G c (ofPath x)) = _
  rw [skewZigzagBaseChangeAlgHom, skewZigzagLift_skewZigzagMk,
    skewZigzagBaseChangePathAlgHom_ofPath]

/-- Scalar extension carries the source scalar action to the target scalar action through the
coefficient homomorphism. -/
@[simp]
theorem skewZigzagBaseChange_algebraMap
    (f : k →+* l) (c : SkewZigzagParameter k G) (a : k) :
    skewZigzagBaseChange G f c (algebraMap k (skewZigzagQuotient k G c) a) =
      algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l))) (f a) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map (f : k →* l))) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f).toAlgebra'
      (fun b y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map (f : k →* l))) (f b) y)
  -- The target is a `k`-algebra via the composite coefficient map.
  change skewZigzagBaseChangeAlgHom G f c (algebraMap k (skewZigzagQuotient k G c) a) =
    ((algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l)))).comp f) a
  exact (skewZigzagBaseChangeAlgHom G f c).commutes a

/-- Mapping a skew-zigzag parameter along the identity homomorphism leaves its relation ideal
unchanged. -/
theorem skewZigzagIdeal_map_id (c : SkewZigzagParameter k G) :
    (skewZigzagIdeal k G (c.map (RingHom.id k : k →* k))).asIdeal =
      (skewZigzagIdeal k G c).asIdeal :=
  congrArg (fun d : SkewZigzagParameter k G => (skewZigzagIdeal k G d).asIdeal) (by
    simpa only [RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_id] using
      SkewZigzagParameter.map_id c)

/-- Mapping a skew-zigzag parameter along a composite or successively gives the same relation
ideal. -/
theorem skewZigzagIdeal_map_comp {m : Type*} [CommRing m]
    (f : k →+* l) (g : l →+* m) (c : SkewZigzagParameter k G) :
    (skewZigzagIdeal m G (c.map (g.comp f : k →* m))).asIdeal =
      (skewZigzagIdeal m G ((c.map (f : k →* l)).map (g : l →* m))).asIdeal :=
  congrArg (fun d : SkewZigzagParameter m G => (skewZigzagIdeal m G d).asIdeal)
    (by
      -- Expose that coercing a composite ring hom to a monoid hom gives the composite of the
      -- coerced monoid homs, so `map_comp` applies.
      rw [show (g.comp f : k →* m) = (g : l →* m).comp (f : k →* l) by
        ext x
        rfl]
      exact SkewZigzagParameter.map_comp (f : k →* l) (g : l →* m) c)

/-- Scalar extension along the identity coefficient homomorphism is the identity map. -/
@[simp]
theorem skewZigzagBaseChange_id (c : SkewZigzagParameter k G) :
    (Ideal.quotientEquivAlgOfEq k
      (I := (skewZigzagIdeal k G (c.map (RingHom.id k : k →* k))).asIdeal)
      (J := (skewZigzagIdeal k G c).asIdeal) (skewZigzagIdeal_map_id G c)).toRingHom.comp
        (skewZigzagBaseChange G (RingHom.id k) c) =
      RingHom.id (skewZigzagQuotient k G c) := by
  apply PathAlgebra.ringHom_ext_of_surjective (skewZigzagMk k G c)
    (skewZigzagMk_surjective k G c)
  · intro a
    simp only [RingHom.comp_apply, skewZigzagBaseChange_algebraMap,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
      AlgEquiv.commutes, RingHom.id_apply]
  · intro x
    rw [RingHom.comp_apply, skewZigzagBaseChange_skewZigzagMk_ofPath,
      skewZigzagMk_apply, skewZigzagMk_apply, RingHom.id_apply]
    simpa only [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_coe] using
        (Ideal.quotientEquivAlgOfEq_mk k (skewZigzagIdeal_map_id G c) (ofPath x))

/-- Scalar extension along a composite coefficient homomorphism is the composite of the two
scalar-extension maps. -/
@[simp]
theorem skewZigzagBaseChange_comp {m : Type*} [CommRing m]
    (f : k →+* l) (g : l →+* m) (c : SkewZigzagParameter k G) :
    (Ideal.Quotient.factor (le_of_eq (skewZigzagIdeal_map_comp G f g c))).comp
        (skewZigzagBaseChange G (g.comp f) c) =
      (skewZigzagBaseChange G g (c.map (f : k →* l))).comp
        (skewZigzagBaseChange G f c) := by
  apply PathAlgebra.ringHom_ext_of_surjective (skewZigzagMk k G c)
    (skewZigzagMk_surjective k G c)
  · intro a
    simp only [RingHom.comp_apply]
    rw [skewZigzagBaseChange_algebraMap, skewZigzagBaseChange_algebraMap,
      skewZigzagBaseChange_algebraMap]
    exact (Ideal.quotientEquivAlgOfEq m
      (I := (skewZigzagIdeal m G (c.map (g.comp f : k →* m))).asIdeal)
      (J := (skewZigzagIdeal m G ((c.map (f : k →* l)).map (g : l →* m))).asIdeal)
      (skewZigzagIdeal_map_comp G f g c)).commutes (g (f a))
  · intro x
    simp only [RingHom.comp_apply]
    rw [skewZigzagBaseChange_skewZigzagMk_ofPath,
      skewZigzagBaseChange_skewZigzagMk_ofPath,
      skewZigzagBaseChange_skewZigzagMk_ofPath, skewZigzagMk_apply,
      skewZigzagMk_apply]
    exact Ideal.quotientEquivAlgOfEq_mk m
      (I := (skewZigzagIdeal m G (c.map (g.comp f : k →* m))).asIdeal)
      (J := (skewZigzagIdeal m G ((c.map (f : k →* l)).map (g : l →* m))).asIdeal)
      (skewZigzagIdeal_map_comp G f g c) (ofPath x)

end Quotient

end TauCeti
