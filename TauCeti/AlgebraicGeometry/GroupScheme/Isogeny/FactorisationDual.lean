/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Degree
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp
import TauCeti.AlgebraicGeometry.GroupScheme.Cokernel
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.CategoryTheory.Preadditive.NSMul

/-!
# The factorisation dual of an isogeny of commutative group schemes

For a locally finitely presented isogeny `f : A ⟶ B` of commutative group schemes of
constant degree `n`, its kernel is killed by `n`.
Multiplication by `n` therefore factors uniquely through `f`, giving a homomorphism
`factorisationDual f hf : B ⟶ A`. Both composites are multiplication by `n`, on their
respective group schemes. The construction uses fpqc descent, so also applies in
characteristics dividing the degree and over nonreduced bases.

Uniqueness of the factorisation gives the formal properties of the dual. It reverses
composition, commutes with arbitrary base change, and is computed on multiplication maps. If
multiplication by `n` on `A` is an isogeny of degree `n * k` and multiplication by `n` on `B` is
finite, the dual is an isogeny of degree `k`. When the dual again has degree `n`, its own
factorisation dual is `f`.

For elliptic curves, apply this API to `A = E.toCommGrp` and `B = E'.toCommGrp`;
local finite presentation is automatic, and multiplication by `n` has degree `n²`. This gives the
factorisation construction before comparison with the Picard dual.

## Main definitions

* `TauCeti.GroupScheme.factorisationDual`: the factorisation dual `B ⟶ A` of an isogeny
  `f : A ⟶ B` of constant degree.

## Main results

* `TauCeti.GroupScheme.comp_factorisationDual`, `TauCeti.GroupScheme.factorisationDual_comp`:
  both composites of `f` with its dual are multiplication by the degree.
* `TauCeti.GroupScheme.eq_factorisationDual`: uniqueness of the factorisation.
* `TauCeti.GroupScheme.isogenyOfDegree_factorisationDual`: the dual is an isogeny, and its
  degree.
* `TauCeti.GroupScheme.factorisationDual_factorisationDual`: involutivity.
* `TauCeti.GroupScheme.factorisationDual_comp_eq_comp`: the dual of a composite is the composite
  of the duals in the opposite order.
* `TauCeti.GroupScheme.factorisationDual_intCast`: the dual of multiplication by `m`.
* `TauCeti.GroupScheme.pullback_mapCommGrp_map_factorisationDual`: compatibility with arbitrary
  base change.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.GroupScheme

variable {S : Scheme.{u}} {A B : CommGrp (Over S)}
  (f : A ⟶ B) [LocallyOfFinitePresentation f.hom.hom.hom.left] {n : ℕ}

private theorem kernel_ι_comp_natCast_eq_zero (hf : IsogenyOfDegree f.hom n) :
    kernel.ι f.hom ≫ (n : End A).asHom.hom = 0 := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, CommGrp.natCast_hom_hom_hom, MonObj.comp_pow,
    Category.comp_id, hf.kernel_ι_pow_eq_one]
  simp [CategoryTheory.Hom.one_def]

private noncomputable def factorisationLift (hf : IsogenyOfDegree f.hom n) :=
  have := hf.isIsogeny.isFinite
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  CokernelCofork.IsColimit.desc' (isColimitKernelCofork f.hom)
    (n : End A).asHom.hom (kernel_ι_comp_natCast_eq_zero f hf)

/-- The factorisation dual of a constant-degree isogeny, characterized by
`comp_factorisationDual`. It is a homomorphism from `B` to `A`. -/
noncomputable def factorisationDual (hf : IsogenyOfDegree f.hom n) :
    B ⟶ A :=
  InducedCategory.homMk (factorisationLift f hf).1

/-- Composing `f : A ⟶ B` with its factorisation dual `B ⟶ A` is `[n]` on `A`. -/
@[reassoc (attr := simp)]
theorem comp_factorisationDual (hf : IsogenyOfDegree f.hom n) :
    f ≫ factorisationDual f hf = (n : End A).asHom :=
  InducedCategory.hom_ext (factorisationLift f hf).2

/-- A homomorphism `B ⟶ A` whose composite with `f` is `[n]` equals the factorisation dual. -/
theorem eq_factorisationDual (hf : IsogenyOfDegree f.hom n)
    (g : B ⟶ A) (hg : f ≫ g = (n : End A).asHom) :
    g = factorisationDual f hf := by
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  have := Flat.epi_of_flat_of_surjective f.hom.hom.hom.left
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi f.hom.hom.hom.left).mp
  exact congrArg (fun k ↦ k.hom.hom.hom.left) (hg.trans (comp_factorisationDual f hf).symm)

/-- Composing the factorisation dual `B ⟶ A` with `f : A ⟶ B` is `[n]` on `B`. -/
@[reassoc (attr := simp)]
theorem factorisationDual_comp (hf : IsogenyOfDegree f.hom n) :
    factorisationDual f hf ≫ f = (n : End B).asHom := by
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  have := Flat.epi_of_flat_of_surjective f.hom.hom.hom.left
  have : Epi f.hom.hom.hom := Over.epi_of_epi_left _
  apply CommGrp.hom_ext
  apply (cancel_epi f.hom.hom.hom).mp
  have h := congrArg (fun k ↦ k.hom.hom.hom)
    (congrArg (fun k ↦ k ≫ f) (comp_factorisationDual f hf))
  simpa only [CommGrp.comp_hom, Grp.comp_hom_hom, Category.assoc,
    CommGrp.natCast_hom_hom_hom, MonObj.pow_comp, MonObj.comp_pow,
    Category.id_comp, Category.comp_id] using h

/-! ### Isogeny, degree and involutivity -/

/-- **The factorisation dual is an isogeny.** Let `f : A ⟶ B` be an isogeny of degree `n`. If
multiplication by `n` on `A` is an isogeny of degree `n * k` and multiplication by `n` on `B` is
finite, then the factorisation dual `B ⟶ A` is an isogeny of degree `k`. For elliptic curves,
multiplication by `n` has degree `n²`, so the dual of an isogeny of degree `n` again has degree
`n`. -/
theorem isogenyOfDegree_factorisationDual (hf : IsogenyOfDegree f.hom n) {k : ℕ}
    (hA : IsogenyOfDegree (n : End A).asHom.hom (n * k))
    [IsFinite (n : End B).asHom.hom.hom.hom.left] :
    IsogenyOfDegree (factorisationDual f hf).hom k := by
  have := hf.isIsogeny.isFinite
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  have := hA.isIsogeny.isFinite
  have := hA.isIsogeny.flat
  have := hA.isIsogeny.surjective
  -- The composites of `f` with its dual, as morphisms of schemes, are multiplication by `n`.
  have hA' : f.hom.hom.hom.left ≫ (factorisationDual f hf).hom.hom.hom.left =
      (n : End A).asHom.hom.hom.hom.left :=
    congrArg (fun g ↦ g.hom.hom.hom.left) (comp_factorisationDual f hf)
  have hB' : (factorisationDual f hf).hom.hom.hom.left ≫ f.hom.hom.hom.left =
      (n : End B).asHom.hom.hom.hom.left :=
    congrArg (fun g ↦ g.hom.hom.hom.left) (factorisationDual_comp f hf)
  have : IsFinite (factorisationDual f hf).hom.hom.hom.left := by
    have : IsFinite ((factorisationDual f hf).hom.hom.hom.left ≫ f.hom.hom.hom.left) := by
      rw [hB']; infer_instance
    exact IsFinite.of_comp _ f.hom.hom.hom.left
  have : Flat ((factorisationDual f hf).hom.hom.hom.left) := by
    have : Flat (f.hom.hom.hom.left ≫ (factorisationDual f hf).hom.hom.hom.left) := by
      rw [hA']; infer_instance
    exact Flat.of_comp_surjective f.hom.hom.hom.left _
  have : Surjective ((factorisationDual f hf).hom.hom.hom.left) := by
    have : Surjective (f.hom.hom.hom.left ≫ (factorisationDual f hf).hom.hom.hom.left) := by
      rw [hA']; infer_instance
    exact Surjective.of_comp f.hom.hom.hom.left _
  refine ⟨(isIsogeny_iff _).mpr ⟨‹_›, ‹_›, ‹_›⟩, fun s ↦ ?_⟩
  -- Degrees multiply along `f ≫ f̂ = [n]`, and the degree `n` of `f` is positive.
  have hn : 0 < n := hf.degree_eq s ▸ degree_pos f.hom s
  have h := degree_comp f.hom (factorisationDual f hf).hom s
  rw [← CommGrp.comp_hom, comp_factorisationDual, hA.degree_eq,
    hf.degree_eq] at h
  exact (Nat.eq_of_mul_eq_mul_left hn h).symm

/-- **The factorisation dual is involutive.** If the factorisation dual of an isogeny `f` of
degree `n` is again an isogeny of degree `n`, then its own factorisation dual is `f`. -/
@[simp]
theorem factorisationDual_factorisationDual (hf : IsogenyOfDegree f.hom n)
    [LocallyOfFinitePresentation (factorisationDual f hf).hom.hom.hom.left]
    (hf' : IsogenyOfDegree (factorisationDual f hf).hom n) :
    factorisationDual (factorisationDual f hf) hf' = f :=
  (eq_factorisationDual _ hf' f (factorisationDual_comp f hf)).symm

/-! ### Composition and multiplication maps -/

/-- **The factorisation dual reverses composition.** For isogenies `f : A ⟶ B` of degree `m`
and `g : B ⟶ C` of degree `n`, the factorisation dual of `f ≫ g : A ⟶ C`, of degree `m * n`, is
the composite `C ⟶ B ⟶ A` of the factorisation duals of `g` and of `f`. -/
theorem factorisationDual_comp_eq_comp {C : CommGrp (Over S)} (g : B ⟶ C)
    [LocallyOfFinitePresentation g.hom.hom.hom.left]
    [LocallyOfFinitePresentation (f ≫ g).hom.hom.hom.left] {m : ℕ}
    (hf : IsogenyOfDegree f.hom m) (hg : IsogenyOfDegree g.hom n)
    (hfg : IsogenyOfDegree (f ≫ g).hom (m * n)) :
    factorisationDual (f ≫ g) hfg = factorisationDual g hg ≫ factorisationDual f hf := by
  refine (eq_factorisationDual _ hfg _ ?_).symm
  rw [Category.assoc, comp_factorisationDual_assoc, ← End.natCast_asHom_comp_assoc,
    comp_factorisationDual, ← End.mul_asHom, ← Nat.cast_mul, mul_comm]

/-- **The factorisation dual of a multiplication map.** If multiplication by an integer `m` is an
isogeny of degree `d` with `d = m * k`, then its factorisation dual is multiplication by `k`. For
elliptic curves, multiplication by `m ≠ 0` has degree `m²`, so it is its own factorisation dual. -/
theorem factorisationDual_intCast (m k : ℤ) {d : ℕ}
    [LocallyOfFinitePresentation (m : End A).asHom.hom.hom.hom.left]
    (h : IsogenyOfDegree (m : End A).asHom.hom d) (hd : (d : ℤ) = m * k) :
    factorisationDual (m : End A).asHom h = (k : End A).asHom := by
  refine (eq_factorisationDual _ h _ ?_).symm
  rw [← End.mul_asHom, ← Int.cast_mul, mul_comm, ← hd, Int.cast_natCast]

/-! ### Base change -/

/-- **The factorisation dual commutes with base change.** For an isogeny `f` of degree `n` and a
morphism `s : T ⟶ S`, the factorisation dual of the base change of `f` along `s` is the base change
of the factorisation dual of `f`. -/
theorem pullback_mapCommGrp_map_factorisationDual {T : Scheme.{u}} (s : T ⟶ S)
    (hf : IsogenyOfDegree f.hom n)
    [LocallyOfFinitePresentation ((Over.pullback s).mapCommGrp.map f).hom.hom.hom.left]
    (hf' : IsogenyOfDegree ((Over.pullback s).mapCommGrp.map f).hom n) :
    (Over.pullback s).mapCommGrp.map (factorisationDual f hf) =
      factorisationDual ((Over.pullback s).mapCommGrp.map f) hf' := by
  refine eq_factorisationDual _ hf' _ ?_
  rw [← Functor.map_comp, comp_factorisationDual, Functor.mapCommGrp_map_natCast]

end TauCeti.GroupScheme
