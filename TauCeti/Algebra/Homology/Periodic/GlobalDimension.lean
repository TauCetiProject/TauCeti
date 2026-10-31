/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
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
null-homotopic (`TauCeti.PeriodicComplex.nonempty_homotopy_zero_of_epi`). No positivity of the
period is needed. At period zero, where `ZMod 0` is integer indexing, this is the
K-projectivity of unbounded complexes of projectives in finite global dimension.

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
    have hNZ (j : ZMod n) : HasProjectiveDimensionLT ((kernel π).cycles j) (m + 1) :=
      hS.hasProjectiveDimensionLT_cycles_X₁ (sub_add_cancel j 1) (hL j)
        (hQ.projective_cycles (sub_add_cancel j 1)) m (hZ j)
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
