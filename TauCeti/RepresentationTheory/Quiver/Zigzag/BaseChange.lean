/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge

/-!
# Scalar extension of skew-zigzag parameters

A homomorphism of coefficient rings sends every unit-valued ratio of a skew-zigzag parameter to
a unit-valued ratio over the target.  The resulting parameter has a canonical coefficient map

```text
Z_k(G,c) → Z_l(G,c.map f)
```

which fixes the doubled paths and applies `f : k →+* l` to their coefficients.  This is the
presentation-level scalar-extension map; it does not identify the target with a tensor product.
The parameter construction is functorial in the coefficient homomorphism and is compatible with
gauge transforms, so gauge-equivalent parameters remain gauge equivalent after scalar extension.

The parameter construction only needs a monoid homomorphism.  Injectivity is stated only when the
homomorphism itself is injective, since extending coefficients need not distinguish units without
that hypothesis.

## Main definitions

* `TauCeti.SkewZigzagParameter.map`: apply a monoid homomorphism to every parameter ratio.
* `TauCeti.skewZigzagBaseChange`: the induced coefficient map between relation quotients.

## Main results

* `TauCeti.SkewZigzagParameter.map_injective`: an injective coefficient map distinguishes
  parameters.
* `TauCeti.SkewZigzagParameter.IsGaugeEquivalent.map`: scalar extension preserves gauge
  equivalence.
* `TauCeti.skewZigzagBaseChange_skewZigzagMk_ofPath`: scalar extension fixes every doubled path.
* `TauCeti.skewZigzagBaseChange_algebraMap`: scalar coefficients are transported by the given
  ring homomorphism.

The parameter conventions follow C. Couture, *Skew-Zigzag Algebras*, Sections 3 and 4,
https://arxiv.org/abs/1509.08405; the coefficient map is induced directly from the presented
relations.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u w z

namespace SkewZigzagParameter

section Map

variable {k : Type w} {l : Type z} [Monoid k] [Monoid l]
  {V : Type u} {G : SimpleGraph V}

/-- Apply a monoid homomorphism to every ratio of a skew-zigzag parameter. -/
def map (f : k →* l) (c : SkewZigzagParameter k G) : SkewZigzagParameter l G where
  ratio _ _ _ h h' := Units.map f (c.ratio h h')
  ratio_self := by intro i j h; simp
  ratio_inv := by
    intro i j j' h h'
    rw [← map_mul, c.ratio_inv]
    exact map_one (Units.map f)
  ratio_cocycle := by
    intro i j j' j'' h h' h''
    rw [← map_mul, ← map_mul, c.ratio_cocycle]
    exact map_one (Units.map f)

/-- Scalar extension applies the coefficient homomorphism to a parameter ratio. -/
@[simp]
theorem map_ratio (f : k →* l) (c : SkewZigzagParameter k G)
    {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') :
    (c.map f).ratio h h' = Units.map f (c.ratio h h') := (rfl)

/-- The constant parameter remains constant after scalar extension. -/
@[simp]
theorem map_one (f : k →* l) :
    map f (1 : SkewZigzagParameter k G) = 1 := by
  ext i j j' h h'
  simp

/-- Mapping a parameter along the identity homomorphism changes nothing. -/
@[simp]
theorem map_id (c : SkewZigzagParameter k G) : c.map (MonoidHom.id k) = c := by
  ext i j j' h h'
  simp

/-- Mapping a parameter along a composite is successive scalar extension. -/
@[simp]
theorem map_comp {m : Type*} [Monoid m] (f : k →* l) (g : l →* m)
    (c : SkewZigzagParameter k G) :
    c.map (g.comp f) = (c.map f).map g := by
  ext i j j' h h'
  simp [Units.map_comp]

/-- An injective coefficient homomorphism induces an injective map on skew-zigzag parameters. -/
theorem map_injective (f : k →* l) (hf : Function.Injective f) :
    Function.Injective (map (G := G) f) := by
  intro c c' h
  apply SkewZigzagParameter.ext
  funext i j j' hi hj
  apply Units.map_injective hf
  exact congrArg (fun d : SkewZigzagParameter l G => d.ratio hi hj) h

end Map

section Gauge

variable {k : Type w} {l : Type z} [CommMonoid k] [CommMonoid l]
  {V : Type u} {G : SimpleGraph V}

/-- Scalar extension commutes with a gauge transform when the arrow labels are extended by the
same coefficient homomorphism. -/
theorem map_gauge (f : k →* l) (c : SkewZigzagParameter k G)
    (a : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) :
    (c.gauge a).map f =
      (c.map f).gauge (fun _ _ b ↦ Units.map f (a b)) := by
  have hscale {i j : V} (h : G.Adj i j) :
      backtrackScale G (fun _ _ b ↦ Units.map f (a b)) h =
        Units.map f (backtrackScale G a h) := by
    rw [backtrackScale_apply, backtrackScale_apply, map_mul]
  ext i j j' h h'
  rw [map_ratio, gauge_ratio, gauge_ratio, hscale, hscale, map_mul, map_div]
  rfl

/-- Gauge-equivalent skew-zigzag parameters remain gauge equivalent after scalar extension. -/
theorem IsGaugeEquivalent.map (f : k →* l) {c c' : SkewZigzagParameter k G}
    (h : c.IsGaugeEquivalent c') :
    (c.map f).IsGaugeEquivalent (c'.map f) := by
  obtain ⟨a, rfl⟩ := isGaugeEquivalent_iff.mp h
  rw [map_gauge]
  exact isGaugeEquivalent_iff.mpr ⟨_, rfl⟩

end Gauge

end SkewZigzagParameter

section Quotient

variable {k : Type w} {l : Type z} {V : Type u}
  [CommRing k] [CommRing l] (G : SimpleGraph V) [Finite V]

private theorem skewZigzagBaseChangePathAlgHom_hcomp
    (f : k →+* l) (c : SkewZigzagParameter k G) {a b d : DoubledQuiver G}
    (p : Path a b) (q : Path d a) :
    (skewZigzagMk l G (c.map f.toMonoidHom) (ofPath ⟨a, b, p⟩) :
        skewZigzagQuotient l G (c.map f.toMonoidHom)) *
      skewZigzagMk l G (c.map f.toMonoidHom)
          (ofPath ⟨d, a, q⟩) =
        skewZigzagMk l G (c.map f.toMonoidHom)
          (ofPath ⟨d, b, q.comp p⟩) := by
  rw [← map_mul, ofPath_mul_ofPath_of_comp]

private theorem skewZigzagBaseChangePathAlgHom_hzero
    (f : k →+* l) (c : SkewZigzagParameter k G)
    {x y : Quiver.TotalPath (DoubledQuiver G)} (h : y.2.1 ≠ x.1) :
    (skewZigzagMk l G (c.map f.toMonoidHom) (ofPath x) :
        skewZigzagQuotient l G (c.map f.toMonoidHom)) *
      skewZigzagMk l G (c.map f.toMonoidHom) (ofPath y) = 0 := by
  rw [← map_mul, ofPath_mul_ofPath_of_not_composable h, map_zero]

private theorem skewZigzagBaseChangePathAlgHom_hone
    (f : k →+* l) (c : SkewZigzagParameter k G) :
    letI : Fintype (DoubledQuiver G) := Fintype.ofFinite _
    (∑ v : DoubledQuiver G,
        (skewZigzagMk l G (c.map f.toMonoidHom)
          (ofPath ⟨v, v, Path.nil⟩) : skewZigzagQuotient l G (c.map f.toMonoidHom))) = 1 := by
  let _ := Fintype.ofFinite (DoubledQuiver G)
  calc
    (∑ v : DoubledQuiver G,
        (skewZigzagMk l G (c.map f.toMonoidHom)
          (ofPath ⟨v, v, Path.nil⟩) : skewZigzagQuotient l G (c.map f.toMonoidHom))) =
        skewZigzagMk l G (c.map f.toMonoidHom)
          (∑ v : DoubledQuiver G, (ofPath ⟨v, v, Path.nil⟩ :
            pathAlgebra l (DoubledQuiver G))) := by
      rw [map_sum]
    _ = skewZigzagMk l G (c.map f.toMonoidHom)
        (∑ v : DoubledQuiver G, vertexIdempotent l v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [vertexIdempotent_eq_ofPath]
    _ = skewZigzagMk l G (c.map f.toMonoidHom) 1 := by rw [one_def]
    _ = 1 := (skewZigzagMk l G (c.map f.toMonoidHom)).map_one

private noncomputable def skewZigzagBaseChangePathAlgHom
    (f : k →+* l) (c : SkewZigzagParameter k G) :
    letI : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
        (fun a x => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) x)
    pathAlgebra k (DoubledQuiver G) →ₐ[k] skewZigzagQuotient l G (c.map f.toMonoidHom) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun a x => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) x)
  exact PathAlgebra.liftAlgHom k
    (fun x => skewZigzagMk l G (c.map f.toMonoidHom) (ofPath x))
    (skewZigzagBaseChangePathAlgHom_hcomp G f c)
    (skewZigzagBaseChangePathAlgHom_hzero G f c)
    (skewZigzagBaseChangePathAlgHom_hone G f c)

private theorem skewZigzagBaseChangePathAlgHom_ofPath
    (f : k →+* l) (c : SkewZigzagParameter k G)
    (x : Quiver.TotalPath (DoubledQuiver G)) :
    letI : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
        (fun a y => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
    skewZigzagBaseChangePathAlgHom G f c (ofPath x) =
      skewZigzagMk l G (c.map f.toMonoidHom) (ofPath x) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
  rw [skewZigzagBaseChangePathAlgHom]
  exact PathAlgebra.liftAlgHom_ofPath k _ _ _ _ x

private theorem skewZigzagBaseChangePathAlgHom_backtrackElem
    (f : k →+* l) (c : SkewZigzagParameter k G) {i j : V} (h : G.Adj i j) :
    letI : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
        (fun a y => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
    skewZigzagBaseChangePathAlgHom G f c (backtrackElem G k h) =
      skewZigzagMk l G (c.map f.toMonoidHom) (backtrackElem G l h) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
  rw [backtrackElem_eq_ofPath, skewZigzagBaseChangePathAlgHom_ofPath,
    backtrackElem_eq_ofPath]

private theorem skewZigzagBaseChangePathAlgHom_relator
    (f : k →+* l) (c : SkewZigzagParameter k G)
    (x : pathAlgebra k (DoubledQuiver G)) (hx : IsSkewZigzagRelator k G c x) :
    letI : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
        (fun a y => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
    skewZigzagBaseChangePathAlgHom G f c x = 0 := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
  cases hx with
  | nonreturn p hlen hne =>
      rw [skewZigzagBaseChangePathAlgHom_ofPath]
      exact skewZigzagMk_ofPath_eq_zero_of_ne l G (c.map f.toMonoidHom) p hlen hne
  | backtrack_ratio h h' =>
      rw [map_sub, map_smul, skewZigzagBaseChangePathAlgHom_backtrackElem,
        skewZigzagBaseChangePathAlgHom_backtrackElem, sub_eq_zero]
      calc
        skewZigzagMk l G (c.map f.toMonoidHom) (backtrackElem G l h) =
            ((c.map f.toMonoidHom).ratio h h' : l) •
              skewZigzagMk l G (c.map f.toMonoidHom) (backtrackElem G l h') :=
          skewZigzagMk_backtrackElem_eq_smul l G (c.map f.toMonoidHom) h h'
        _ = (c.ratio h h' : k) •
              skewZigzagMk l G (c.map f.toMonoidHom) (backtrackElem G l h') := by
          simp only [Algebra.smul_def, SkewZigzagParameter.map_ratio, Units.coe_map]
          rfl
  | long_path y h3 =>
      rw [skewZigzagBaseChangePathAlgHom_ofPath]
      exact skewZigzagMk_ofPath_eq_zero_of_three_le l G (c.map f.toMonoidHom) y h3

private noncomputable def skewZigzagBaseChangeAlgHom
    (f : k →+* l) (c : SkewZigzagParameter k G) :
    letI : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
      ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
        (fun a y => Algebra.commutes (R := l)
          (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
    skewZigzagQuotient k G c →ₐ[k] skewZigzagQuotient l G (c.map f.toMonoidHom) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
  exact skewZigzagLift k G c (skewZigzagBaseChangePathAlgHom G f c)
    (skewZigzagBaseChangePathAlgHom_relator G f c)

/-- The coefficient map on a skew-zigzag relation quotient.

It fixes every doubled path and applies `f` to scalar coefficients.  The codomain carries the
parameter obtained by applying `f` to every unit-valued ratio. -/
noncomputable def skewZigzagBaseChange (f : k →+* l) (c : SkewZigzagParameter k G) :
    skewZigzagQuotient k G c →+* skewZigzagQuotient l G (c.map (f : k →* l)) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
  exact (skewZigzagBaseChangeAlgHom G f c).toRingHom

/-- Scalar extension sends the class of every doubled path to the class of the same path over the
target coefficient ring. -/
@[simp]
theorem skewZigzagBaseChange_skewZigzagMk_ofPath
    (f : k →+* l) (c : SkewZigzagParameter k G)
    (x : Quiver.TotalPath (DoubledQuiver G)) :
    skewZigzagBaseChange G f c (skewZigzagMk k G c (ofPath x)) =
      skewZigzagMk l G (c.map (f : k →* l)) (ofPath x) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun a y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f a) y)
  -- The public map is the underlying ring map of the quotient lift.
  change skewZigzagBaseChangeAlgHom G f c (skewZigzagMk k G c (ofPath x)) = _
  rw [skewZigzagBaseChangeAlgHom, skewZigzagLift_skewZigzagMk,
    skewZigzagBaseChangePathAlgHom_ofPath]
  rfl

/-- Scalar extension carries the source scalar action to the target scalar action through the
coefficient homomorphism. -/
@[simp]
theorem skewZigzagBaseChange_algebraMap
    (f : k →+* l) (c : SkewZigzagParameter k G) (a : k) :
    skewZigzagBaseChange G f c (algebraMap k (skewZigzagQuotient k G c) a) =
      algebraMap l (skewZigzagQuotient l G (c.map (f : k →* l))) (f a) := by
  let _ : Algebra k (skewZigzagQuotient l G (c.map f.toMonoidHom)) :=
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f).toAlgebra'
      (fun b y => Algebra.commutes (R := l)
        (A := skewZigzagQuotient l G (c.map f.toMonoidHom)) (f b) y)
  -- The target is a `k`-algebra via the composite coefficient map.
  change skewZigzagBaseChangeAlgHom G f c (algebraMap k (skewZigzagQuotient k G c) a) =
    ((algebraMap l (skewZigzagQuotient l G (c.map f.toMonoidHom))).comp f) a
  exact (skewZigzagBaseChangeAlgHom G f c).commutes a

end Quotient

end TauCeti
