/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.ProjectiveCycles
public import TauCeti.Algebra.Homology.Periodic.HomotopicallyProjective

/-!
# Periodic complexes of projectives in finite global dimension

In an abelian category with enough projectives in which every object has projective dimension
`< d`, every periodic complex with projective terms is homotopically projective
(`TauCeti.PeriodicComplex.isHomotopicallyProjective_of_projective`). Morphisms out of it into an
acyclic periodic complex are null-homotopic, so the periodic Verdier localization is bijective on
morphisms out of it, and quasi-isomorphisms between such complexes are homotopy equivalences
(`TauCeti.PeriodicComplex.IsHomotopicallyProjective.quasiIso_iff`).

The bound on projective dimensions cannot be dropped: over the dual numbers `k[ε]`, which have
infinite global dimension, multiplication by `ε` on `k[ε]` is a periodic complex with free terms
which is not homotopically projective
(`TauCeti.not_isHomotopicallyProjective_dualNumberPeriodicComplex`).

The proof inducts on a bound `< m + 1` for the projective dimensions of the cycles of the acyclic
target `L` (`TauCeti.PeriodicComplex.nonempty_homotopy_zero_of_hasProjectiveDimensionLT`).
When the cycles of `L` are projective, `L` itself is contractible. Otherwise, choose a
degreewise epimorphism `π : Q ⟶ L` from a contractible complex with projective terms. Its kernel
`N` is acyclic, and the cycles of `N` are syzygies of those of `L`, so they satisfy the bound
`< m`. Given `f : K ⟶ L`, lift it degreewise along `π` to `g : Kⁱ ⟶ Qⁱ`. The failure of `g` to
commute with the differentials is a chain map `K⟦-1⟧ ⟶ N`, null-homotopic by induction, and the
homotopy corrects `g` into a chain map `K ⟶ Q` lifting `f`. Since `Q` is contractible, `f` is
null-homotopic. No positivity of the period is needed. At period zero, where `ZMod 0` is integer
indexing, this is the K-projectivity of unbounded complexes of projectives in finite global
dimension.

## Main results

* `TauCeti.PeriodicComplex.nonempty_homotopy_zero_of_hasProjectiveDimensionLT`: a morphism from a
  periodic complex of projectives to an acyclic periodic complex whose cycles have bounded
  projective dimension is null-homotopic.
* `TauCeti.PeriodicComplex.isHomotopicallyProjective_of_projective`: in finite global dimension,
  periodic complexes of projectives are homotopically projective.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3, Proposition 3.10.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Mathematica **65** (1988),
  121–154, for K-projectivity of complexes of projectives in finite global dimension.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ}

/-- The inductive step: given a degreewise epimorphism `π : Q ⟶ L` from a contractible complex
onto `L`, if every morphism `K⟦-1⟧ ⟶ ker π` is null-homotopic, then so is every `f : K ⟶ L`. -/
private lemma nonempty_homotopy_zero_of_epi {K L Q : CochainComplex C (ZMod n)}
    [∀ i, Projective (K.X i)] (π : Q ⟶ L) [∀ i, Epi (π.f i)] (hQ : Homotopy (𝟙 Q) 0)
    (hN : ∀ u : K⟦(-1 : ℤ)⟧ ⟶ kernel π, Nonempty (Homotopy u 0)) (f : K ⟶ L) :
    Nonempty (Homotopy f 0) := by
  -- Lift `f` degreewise along `π`.
  let g (i : ZMod n) : K.X i ⟶ Q.X i := Projective.factorThru (f.f i) (π.f i)
  have hg (i : ZMod n) : g i ≫ π.f i = f.f i := Projective.factorThru_comp _ _
  have hgX (a b : ZMod n) (h : a = b) :
      (K.XIsoOfEq h).hom ≫ g b = g a ≫ (Q.XIsoOfEq h).hom := by
    subst h
    simp
  -- The failure of `g` to commute with the differentials, as a chain map out of `K⟦-1⟧`.
  let u : K⟦(-1 : ℤ)⟧ ⟶ Q :=
    { f i := g (i + ((-1 : ℤ) : ZMod n)) ≫ Q.d _ i - K.d _ i ≫ g i
      comm' := by
        rintro i _ rfl
        have hd (a b : ZMod n) (h : a = b) :
            K.d (i + ((-1 : ℤ) : ZMod n)) a ≫ g a ≫ Q.d a (i + 1) =
              K.d (i + ((-1 : ℤ) : ZMod n)) b ≫ g b ≫ Q.d b (i + 1) := by
          subst h
          rfl
        simp [hd i (i + 1 + ((-1 : ℤ) : ZMod n)) (by push_cast; ring)] }
  have hu : u ≫ π = 0 := by
    ext i
    simp only [u, comp_f, Preadditive.sub_comp, Category.assoc, ← π.comm, hg,
      reassoc_of% hg, f.comm, sub_self, zero_f]
  obtain ⟨H⟩ := hN (kernel.lift π u hu)
  -- A null-homotopy of `u` whose components are killed by `π`.
  let H' : Homotopy u 0 :=
    (Homotopy.ofEq (kernel.lift_ι π u hu).symm).trans
      ((H.compRight (kernel.ι π)).trans (Homotopy.ofEq zero_comp))
  have hH' (i j : ZMod n) : H'.hom i j ≫ π.f j = 0 := by
    simp [H', ← comp_f]
  let e (i : ZMod n) : K.X i ⟶ (K⟦(-1 : ℤ)⟧).X (i + 1) :=
    (K.XIsoOfEq (by push_cast; ring)).hom
  -- The corrected lift of `f`, a chain map `K ⟶ Q`.
  let g' : K ⟶ Q :=
    { f i := g i - e i ≫ H'.hom (i + 1) i
      comm' := by
        rintro i _ rfl
        have H₁ := H'.comm (i + 1)
        rw [dNext_eq _ (show (ComplexShape.up (ZMod n)).Rel (i + 1) (i + 1 + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up (ZMod n)).Rel i (i + 1) from rfl)] at H₁
        have H₂ := congr(e i ≫ $H₁)
        simp only [u, e, zero_f, add_zero, Preadditive.comp_sub, Preadditive.comp_add,
          shiftFunctor_obj_d', Int.reduceNeg, Int.negOnePow_neg, Int.negOnePow_one,
          Units.neg_smul, one_smul, Preadditive.neg_comp, Preadditive.comp_neg,
          XIsoOfEq_hom_comp_d_assoc, reassoc_of% hgX] at H₂
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc, e]
        rw [XIsoOfEq_hom_comp_d, ← K.d_comp_XIsoOfEq_hom
          (show i + 1 = i + 1 + 1 + ((-1 : ℤ) : ZMod n) by push_cast; ring), Category.assoc] at H₂
        rw [sub_eq_sub_iff_sub_eq_sub, H₂]
        abel }
  have hg' : g' ≫ π = f := by
    ext i
    simp [g', hg, hH']
  exact ⟨(Homotopy.ofEq (by simp [hg'])).trans
    (((hQ.compLeft g').compRight π).trans (Homotopy.ofEq (by simp)))⟩

variable [EnoughProjectives C]

/-- The induction on the projective dimension of the cycles of the target. -/
private lemma nonempty_homotopy_zero_of_hasProjectiveDimensionLT_succ (m : ℕ) :
    ∀ {K L : CochainComplex C (ZMod n)} [∀ i, Projective (K.X i)], L.Acyclic →
      (∀ i, HasProjectiveDimensionLT (L.cycles i) (m + 1)) →
        ∀ f : K ⟶ L, Nonempty (Homotopy f 0) := by
  induction m with
  | zero =>
    intro K L _ hL hZ f
    obtain ⟨h⟩ := hL.nonempty_homotopy_id_zero_of_projective_cycles
      fun i ↦ projective_iff_hasProjectiveDimensionLT_one.mpr (hZ i)
    exact ⟨(Homotopy.ofEq (Category.comp_id f).symm).trans
      ((h.compLeft f).trans (Homotopy.ofEq Limits.comp_zero))⟩
  | succ m ih =>
    intro K L _ hL hZ f
    obtain ⟨Q, π, _, _, ⟨hQ⟩⟩ :=
      L.exists_projective_contractible_epi_f (fun i ↦ ⟨i + 1, rfl⟩)
        (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    have : Epi π := epi_of_epi_f π inferInstance
    -- The short exact sequence `0 ⟶ ker π ⟶ Q ⟶ L ⟶ 0`.
    have hS : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π) }
    have : QuasiIso π := ⟨fun i ↦ (quasiIsoAt_iff_exactAt π i (hQ.acyclic i)).mpr (hL i)⟩
    have hN : (kernel π).Acyclic := hS.acyclic_X₁ this
    have hNZ := hS.hasProjectiveDimensionLT_cycles_X₁ (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) hL
      (fun j ↦ hQ.projective_cycles (show (ComplexShape.up (ZMod n)).Rel (j - 1) j from
        sub_add_cancel j 1)) m hZ
    have : ∀ i, Projective ((K⟦(-1 : ℤ)⟧).X i) := fun i ↦
      inferInstanceAs (Projective (K.X _))
    exact nonempty_homotopy_zero_of_epi π hQ (ih hN hNZ) f

/-- A morphism from a periodic complex of projectives to an acyclic periodic complex whose cycles
all have projective dimension `< d` is null-homotopic. -/
theorem nonempty_homotopy_zero_of_hasProjectiveDimensionLT {K L : CochainComplex C (ZMod n)}
    [∀ i, Projective (K.X i)] (hL : L.Acyclic) (d : ℕ)
    (hd : ∀ i, HasProjectiveDimensionLT (L.cycles i) d) (f : K ⟶ L) :
    Nonempty (Homotopy f 0) :=
  nonempty_homotopy_zero_of_hasProjectiveDimensionLT_succ d hL
    (fun i ↦ hasProjectiveDimensionLT_of_ge _ d (d + 1) (by lia)) f

/-- In an abelian category with enough projectives in which every object has projective dimension
`< d`, every periodic complex of projectives is homotopically projective. -/
theorem isHomotopicallyProjective_of_projective (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) (K : CochainComplex C (ZMod n))
    [∀ i, Projective (K.X i)] : IsHomotopicallyProjective K where
  nonempty_homotopy_zero f hL :=
    nonempty_homotopy_zero_of_hasProjectiveDimensionLT hL d (fun _ ↦ hd _) f

end TauCeti.PeriodicComplex
