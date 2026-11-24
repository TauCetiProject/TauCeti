/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructible
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Sections
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.Modules.Localization

/-!
# The nonvanishing locus of a section of an invertible sheaf

Let `M` be an invertible sheaf on a scheme `X` and `s` a section of `M` over an open `U`. The
**nonvanishing locus** `X_s` is the set of points `x ∈ U` at which the germ of `s` generates the
stalk `M_x`, equivalently at which `s` does not vanish in the fibre `M_x ⊗ κ(x)`. Over an open `V`
on which `M` is trivialized, `s` is a regular function times the basis section, and `X_s ∩ V` is
the basic open set of that function; in particular `X_s` is open. It generalizes the basic open
set `X_f` of a regular function, the case of the structure sheaf.

These open sets are the ones through which positivity of line bundles is defined: `M` is globally
generated when the sets `X_s` of its global sections cover `X`, and ample when `X` is
quasi-compact and the sets `X_s` that are affine, for global sections `s` of the positive tensor
powers of `M`, cover `X`.

The section `s` is a basis of `M` exactly over its nonvanishing locus: an open `W ⊆ U` lies in
`X_s` if and only if, on every open `W' ⊆ W`, every section of `M` is a unique regular multiple
of the restriction of `s`. In other words, `s` trivializes `M` over `X_s`.

On an affine open `U`, the nonvanishing locus of every section over `U` is affine: over a cover of
`U` by basic opens trivializing `M` it is a basic open of each member. Moreover the sections over
`U` generate every stalk, since the sections over a basic open `D(f) ⊆ U` are the localization at
`f` of the sections over `U`. These are the two facts making every invertible sheaf on an affine
scheme ample.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`: the open set `X_s` of points at which the
  germ of `s` generates the stalk.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_eq_basicOpen`: on the domain of a rank-one
  trivialization, `X_s` is the basic open set of the coordinate of `s`;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_map` and
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_smul`: restriction intersects `X_s` with the
  smaller open, and `X_{r s} = X_r ∩ X_s` for a regular function `r`;
* `AlgebraicGeometry.Scheme.Modules.le_nonvanishingLocus_iff`: `s` is a basis of `M` exactly over
  open subsets of `X_s`;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_hom_app`: the nonvanishing locus is
  invariant under isomorphisms of invertible sheaves;
* `AlgebraicGeometry.Scheme.Modules.range_nonvanishingLocus_eq_of_iso`: isomorphic invertible
  sheaves have the same nonvanishing loci of sections over each open;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_unit`: on the structure sheaf, `X_r` is the
  basic open set of the regular function `r`;
* `AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingLocus`: if `s|_V = f • e` with
  `e` nonvanishing on `V`, then `X_s ∩ V` is the basic open set of `f`;
* `AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_forall_isAffineOpen_nonvanishingLocus`:
  a scheme covered by affine nonvanishing loci of global sections of `M` is quasi-separated;
* `AlgebraicGeometry.IsAffineOpen.nonvanishingLocus`: on an affine open, `X_s` is affine;
* `AlgebraicGeometry.Scheme.Modules.exists_mem_nonvanishingLocus_of_isAffineOpen`: every point of
  an affine open `U` lies in `X_s` for some section `s` over `U`;
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_restrictAppIso_inv`,
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_pullbackSections`, and
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_pullbackSectionsLE`: the nonvanishing locus
  of a restricted or pulled-back section is the preimage of the nonvanishing locus;
* `AlgebraicGeometry.Scheme.Modules.exists_finite_affine_cover_le_nonvanishingLocus` and
  `AlgebraicGeometry.Scheme.Modules.isRetrocompact_nonvanishingLocus`: quasi-compact opens admit
  finite trivializing affine covers, and the nonvanishing locus of a section over a retrocompact
  (in particular global) open is retrocompact.

## References

* The Stacks Project, Tag 01CT (the open `X_s` attached to a section of an invertible sheaf) and
  Tag 01PS (ample invertible sheaves).
* The Stacks Project, *Properties of Schemes*, the section on ample invertible sheaves (around
  Tag 01PS), for the affineness of `X_s` on an affine scheme.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

/-- On the domain of a rank-one trivialization, the germ of a section generates the stalk exactly
when the germ of its coordinate is a unit of the local ring. -/
theorem span_germ_eq_top_iff_isUnit {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) {x : X} (hx : x ∈ W) :
    Submodule.span (X.presheaf.stalk x) {M.presheaf.germ W x hx s} = ⊤ ↔
      IsUnit (X.presheaf.germ W x hx (trivializationCoordinate M t i s)) := by
  conv_lhs => rw [eq_trivializationCoordinate_smul_map_trivializationGenerator M t i s]
  rw [germ_smul, TopCat.Presheaf.germ_res_apply, span_smul_eq_top_iff,
    span_germ_trivializationGenerator M x t (i.le hx)]
  exact and_iff_left rfl

/-- The **nonvanishing locus** `X_s` of a section `s` of an invertible sheaf over `U`: the open
set of points of `U` at which the germ of `s` generates the stalk. -/
def nonvanishingLocus {U : X.Opens} (s : Γ(M, U)) : X.Opens where
  carrier := {x | ∃ hx : x ∈ U,
    Submodule.span (X.presheaf.stalk x) {M.presheaf.germ U x hx s} = ⊤}
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxU, hx⟩
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
    let i : U ⊓ V ⟶ V := homOfLE inf_le_right
    let j : U ⊓ V ⟶ U := homOfLE inf_le_left
    -- Near `x`, the locus contains the basic open set of the coordinate of `s`.
    have key {y : X} (hy : y ∈ U ⊓ V) :
        Submodule.span (X.presheaf.stalk y) {M.presheaf.germ U y (j.le hy) s} = ⊤ ↔
          y ∈ X.basicOpen (trivializationCoordinate M t i (M.presheaf.map j.op s)) := by
      rw [X.mem_basicOpen _ _ hy, ← span_germ_eq_top_iff_isUnit M t i _ hy,
        TopCat.Presheaf.germ_res_apply]
    exact ⟨_, fun y hy ↦ ⟨_, (key (X.basicOpen_le _ hy)).mpr hy⟩, (X.basicOpen _).isOpen,
      (key ⟨hxU, hxV⟩).mp hx⟩

variable {M}

/-- A point lies in the nonvanishing locus of `s` exactly when it lies in the domain of `s` and the
germ of `s` there generates the stalk. -/
theorem mem_nonvanishingLocus_iff {U : X.Opens} {s : Γ(M, U)} {x : X} :
    x ∈ M.nonvanishingLocus s ↔
      ∃ hx : x ∈ U, Submodule.span (X.presheaf.stalk x) {M.presheaf.germ U x hx s} = ⊤ :=
  Iff.rfl

/-- A point of the domain of `s` lies in its nonvanishing locus exactly when the germ of `s`
generates the stalk there. -/
theorem mem_nonvanishingLocus_iff_of_mem {U : X.Opens} {s : Γ(M, U)} {x : X} (hx : x ∈ U) :
    x ∈ M.nonvanishingLocus s ↔
      Submodule.span (X.presheaf.stalk x) {M.presheaf.germ U x hx s} = ⊤ :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hx, h⟩⟩

/-- The nonvanishing locus of a section over `U` is contained in `U`. -/
theorem nonvanishingLocus_le {U : X.Opens} (s : Γ(M, U)) : M.nonvanishingLocus s ≤ U :=
  fun _ ⟨hx, _⟩ ↦ hx

/-- On the domain of a rank-one trivialization, the nonvanishing locus of a section is the basic
open set of its coordinate. -/
theorem nonvanishingLocus_eq_basicOpen {U V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : U ⟶ V)
    (s : Γ(M, U)) :
    M.nonvanishingLocus s = X.basicOpen (trivializationCoordinate M t i s) := by
  ext x
  refine ⟨fun ⟨hx, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · exact (X.mem_basicOpen _ _ hx).mpr ((span_germ_eq_top_iff_isUnit M t i s hx).mp h)
  · have hx := X.basicOpen_le _ h
    exact ⟨hx, (span_germ_eq_top_iff_isUnit M t i s hx).mpr ((X.mem_basicOpen _ _ hx).mp h)⟩

/-- The nonvanishing locus of a restricted section is the intersection of the smaller open with
the nonvanishing locus of the section. -/
@[simp]
theorem nonvanishingLocus_map {U W : X.Opens} (j : W ⟶ U) (s : Γ(M, U)) :
    M.nonvanishingLocus (M.presheaf.map j.op s) = W ⊓ M.nonvanishingLocus s := by
  ext x
  refine ⟨fun ⟨hx, h⟩ ↦ ⟨hx, j.le hx, ?_⟩, fun ⟨hx, _, h⟩ ↦ ⟨hx, ?_⟩⟩
  · rwa [TopCat.Presheaf.germ_res_apply] at h
  · rwa [TopCat.Presheaf.germ_res_apply]

/-- The nonvanishing locus of a regular multiple `r • s` is the intersection of the basic open set
of `r` with the nonvanishing locus of `s`. -/
@[simp]
theorem nonvanishingLocus_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(M, U)) :
    M.nonvanishingLocus (r • s) = X.basicOpen r ⊓ M.nonvanishingLocus s := by
  ext x
  refine ⟨fun ⟨hx, h⟩ ↦ ?_, fun ⟨hr, hx, h⟩ ↦ ⟨hx, ?_⟩⟩
  · rw [germ_smul, span_smul_eq_top_iff] at h
    exact ⟨(X.mem_basicOpen _ _ hx).mpr h.1, hx, h.2⟩
  · rw [germ_smul, span_smul_eq_top_iff]
    exact ⟨(X.mem_basicOpen _ _ hx).mp hr, h⟩

/-- The zero section vanishes everywhere. -/
@[simp]
theorem nonvanishingLocus_zero (U : X.Opens) : M.nonvanishingLocus (0 : Γ(M, U)) = ⊥ := by
  rw [← zero_smul Γ(X, U) (0 : Γ(M, U)), nonvanishingLocus_smul, X.basicOpen_zero, bot_inf_eq]

/-- The basis section of a rank-one trivialization over `V` vanishes nowhere on `V`. -/
@[simp]
theorem nonvanishingLocus_trivializationGenerator {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) :
    M.nonvanishingLocus (trivializationGenerator M t) = V := by
  rw [nonvanishingLocus_eq_basicOpen t (𝟙 V), trivializationCoordinate_trivializationGenerator,
    X.basicOpen_one]

/-- A section is a nonzerodivisor for the regular functions over any open contained in its
nonvanishing locus. -/
theorem injective_smul_of_le_nonvanishingLocus {U : X.Opens} {s : Γ(M, U)}
    (h : U ≤ M.nonvanishingLocus s) : Function.Injective fun r : Γ(X, U) ↦ r • s := by
  intro r r' hrr'
  refine TopCat.Presheaf.section_ext X.sheaf U r r' fun x hx ↦ ?_
  have hs := (mem_nonvanishingLocus_iff_of_mem hx).mp (h hx)
  refine (bijective_toSpanSingleton_of_span_eq_top M x hs).1 ?_
  have hgerm := congrArg (M.presheaf.germ U x hx) hrr'
  simp only [germ_smul] at hgerm
  exact hgerm

/-- Every section over an open contained in the nonvanishing locus of `s` is a regular multiple
of `s`. -/
theorem surjective_smul_of_le_nonvanishingLocus {U : X.Opens} {s : Γ(M, U)}
    (h : U ≤ M.nonvanishingLocus s) : Function.Surjective fun r : Γ(X, U) ↦ r • s := by
  intro m
  -- Near each point `x` of `U`, the germ of `m` is a multiple of the germ of `s`, so `m` is a
  -- multiple `r x • s` on a neighbourhood `N x ⊆ U` of `x`.
  have hloc (x : U) : ∃ (N : X.Opens) (_ : (x : X) ∈ N) (k : N ⟶ U) (r : Γ(X, N)),
      r • M.presheaf.map k.op s = M.presheaf.map k.op m := by
    have hs := (mem_nonvanishingLocus_iff_of_mem x.property).mp (h x.property)
    obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff _ _).mp hs
        (M.presheaf.germ U x x.property m)
    obtain ⟨W, hxW, r, rfl⟩ := X.presheaf.exists_germ_eq a
    let p : W ⊓ U ⟶ W := homOfLE inf_le_left
    let q : W ⊓ U ⟶ U := homOfLE inf_le_right
    have hxWU : (x : X) ∈ W ⊓ U := ⟨hxW, x.property⟩
    have ha' : M.presheaf.germ (W ⊓ U) x hxWU
        (X.presheaf.map p.op r • M.presheaf.map q.op s) =
          M.presheaf.germ (W ⊓ U) x hxWU (M.presheaf.map q.op m) := by
      rw [germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
        TopCat.Presheaf.germ_res_apply]
      exact ha
    obtain ⟨N, hxN, k, k', hk⟩ := M.presheaf.germ_eq _ hxWU hxWU _ _ ha'
    rw [Subsingleton.elim k' k] at hk
    refine ⟨N, hxN, k ≫ q, X.presheaf.map (k ≫ p).op r, ?_⟩
    simpa only [map_smul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hk
  choose N hxN k r hr using hloc
  have hcover : U ≤ iSup N := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
  -- The local coefficients agree on overlaps, because `s` is a nonzerodivisor there.
  have hres {x : U} {O : X.Opens} (j : O ⟶ N x) (a : O ⟶ U) :
      X.presheaf.map j.op (r x) • M.presheaf.map a.op s = M.presheaf.map a.op m := by
    obtain rfl : a = j ≫ k x := Subsingleton.elim _ _
    have hx := congrArg (M.presheaf.map j.op) (hr x)
    simpa only [map_smul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hx
  obtain ⟨c, hc, -⟩ : ∃! c : Γ(X, U), ∀ x, X.presheaf.map (k x).op c = r x :=
    X.sheaf.existsUnique_gluing' N U k hcover r fun x y ↦ by
      let a : N x ⊓ N y ⟶ U := Opens.infLELeft _ _ ≫ k x
      have ha : N x ⊓ N y ≤ M.nonvanishingLocus (M.presheaf.map a.op s) := by
        rw [nonvanishingLocus_map]
        exact le_inf le_rfl (a.le.trans h)
      exact injective_smul_of_le_nonvanishingLocus ha
        ((hres _ a).trans (hres (Opens.infLERight _ _) a).symm)
  -- The glued coefficient works, since both sides have the same germ at every point of `U`.
  refine ⟨c, TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    U _ _ fun x hx ↦ ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (k ⟨x, hx⟩) _ (hxN ⟨x, hx⟩),
    ← TopCat.Presheaf.germ_res_apply M.presheaf (k ⟨x, hx⟩) _ (hxN ⟨x, hx⟩)]
  exact congrArg _ ((map_smul M _ c s).trans
    ((congrArg (· • _) (hc ⟨x, hx⟩)).trans (hr ⟨x, hx⟩)))

/-- **A section is a basis exactly over its nonvanishing locus.** An open `W ⊆ U` lies in the
nonvanishing locus of `s` if and only if, on every open `W' ⊆ W`, every section of `M` is a unique
regular multiple of the restriction of `s`. -/
theorem le_nonvanishingLocus_iff {U W : X.Opens} (s : Γ(M, U)) (i : W ⟶ U) :
    W ≤ M.nonvanishingLocus s ↔ ∀ (W' : X.Opens) (j : W' ⟶ W),
      Function.Bijective fun r : Γ(X, W') ↦ r • M.presheaf.map (j ≫ i).op s := by
  refine ⟨fun h W' j ↦ ?_, fun h x hxW ↦ ⟨i.le hxW, ?_⟩⟩
  · have h' : W' ≤ M.nonvanishingLocus (M.presheaf.map (j ≫ i).op s) := by
      rw [nonvanishingLocus_map]
      exact le_inf le_rfl (j.le.trans h)
    exact ⟨injective_smul_of_le_nonvanishingLocus h', surjective_smul_of_le_nonvanishingLocus h'⟩
  · -- Every germ of `M` at `x` is the germ of a section over an open `W' ⊆ W`, which is a multiple
    -- of the restriction of `s`.
    refine (Submodule.span_singleton_eq_top_iff _ _).mpr fun m ↦ ?_
    obtain ⟨W'', hxW'', m, rfl⟩ := M.presheaf.exists_germ_eq m
    let j : W'' ⊓ W ⟶ W := homOfLE inf_le_right
    let k : W'' ⊓ W ⟶ W'' := homOfLE inf_le_left
    have hx : x ∈ W'' ⊓ W := ⟨hxW'', hxW⟩
    obtain ⟨r, hr⟩ := (h _ j).2 (M.presheaf.map k.op m)
    beta_reduce at hr
    refine ⟨X.presheaf.germ _ x hx r, ?_⟩
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (j ≫ i) _ hx, ← germ_smul, hr,
      TopCat.Presheaf.germ_res_apply]

/-- The nonvanishing locus is invariant under isomorphisms of invertible sheaves. -/
@[simp]
theorem nonvanishingLocus_hom_app {N : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N] (φ : M ≅ N) {U : X.Opens}
    (s : Γ(M, U)) :
    N.nonvanishingLocus (φ.hom.app U s) = M.nonvanishingLocus s := by
  have hnat {W W' : X.Opens} (j : W' ⟶ W) (y : Γ(M, W)) :
      φ.hom.app W' (M.presheaf.map j.op y) = N.presheaf.map j.op (φ.hom.app W y) := by
    simpa only [mapPresheaf_app, unop_op] using φ.hom.mapPresheaf.naturality_apply j.op y
  -- Multiplication by the image of `s` is multiplication by `s` followed by the bijection `φ`.
  have hbij {W' : X.Opens} (i : W' ⟶ U) :
      (Function.Bijective fun r : Γ(X, W') ↦ r • N.presheaf.map i.op (φ.hom.app U s)) ↔
        Function.Bijective fun r : Γ(X, W') ↦ r • M.presheaf.map i.op s := by
    have hφ : Function.Bijective (φ.hom.app W') :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    have heq : (fun r : Γ(X, W') ↦ r • N.presheaf.map i.op (φ.hom.app U s)) =
        φ.hom.app W' ∘ fun r : Γ(X, W') ↦ r • M.presheaf.map i.op s := by
      ext r
      simp [hnat]
    rw [heq, Function.Bijective.of_comp_iff' hφ]
  refine le_antisymm ?_ ?_
  · refine (le_nonvanishingLocus_iff s (homOfLE (nonvanishingLocus_le _))).mpr fun W' j ↦ ?_
    rw [← hbij]
    exact (le_nonvanishingLocus_iff _ (homOfLE (nonvanishingLocus_le _))).mp le_rfl W' j
  · refine (le_nonvanishingLocus_iff _ (homOfLE (nonvanishingLocus_le _))).mpr fun W' j ↦ ?_
    rw [hbij]
    exact (le_nonvanishingLocus_iff s (homOfLE (nonvanishingLocus_le _))).mp le_rfl W' j

/-- Isomorphic invertible sheaves have the same nonvanishing loci of sections over `U`: the set of
opens `X_s`, for `s` a section over `U`, is invariant under isomorphism. -/
theorem range_nonvanishingLocus_eq_of_iso {N : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N] (φ : M ≅ N) (U : X.Opens) :
    Set.range (M.nonvanishingLocus (U := U)) = Set.range (N.nonvanishingLocus (U := U)) := by
  ext V
  exact ⟨fun ⟨s, hs⟩ ↦ ⟨φ.hom.app U s, (nonvanishingLocus_hom_app φ s).trans hs⟩,
    fun ⟨s, hs⟩ ↦ ⟨φ.symm.hom.app U s, (nonvanishingLocus_hom_app φ.symm s).trans hs⟩⟩

/-- If `e` vanishes nowhere on `V ≤ U` and `s|_V = f • e`, then `X_s ∩ V` is the basic open set
of `f`. -/
theorem basicOpen_eq_inf_nonvanishingLocus {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U))
    {e : Γ(M, V)} (he : V ≤ M.nonvanishingLocus e) {f : Γ(X, V)}
    (hf : f • e = M.presheaf.map i.op s) : X.basicOpen f = V ⊓ M.nonvanishingLocus s := by
  rw [← inf_eq_left.mpr ((X.basicOpen_le f).trans he), ← nonvanishingLocus_smul, hf,
    nonvanishingLocus_map]

/-- A scheme covered by affine nonvanishing loci of global sections of an invertible sheaf is
quasi-separated: two such loci `X_s` and `X_t` meet in the basic open of `X_s` cut out by the
function `t / s`, which is affine. -/
theorem quasiSeparatedSpace_of_forall_isAffineOpen_nonvanishingLocus
    (h : ∀ x : X, ∃ s : Γ(M, ⊤), x ∈ M.nonvanishingLocus s ∧
      IsAffineOpen (M.nonvanishingLocus s)) :
    QuasiSeparatedSpace X := by
  let S := {s : Γ(M, ⊤) // IsAffineOpen (M.nonvanishingLocus s)}
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun s : S ↦ M.nonvanishingLocus s.val)
    (top_unique fun x _ ↦ ?_) (fun s ↦ s.property) fun s t ↦ ?_
  · obtain ⟨s, hxs, hs⟩ := h x
    exact Opens.mem_iSup.mpr ⟨⟨s, hs⟩, hxs⟩
  -- On `X_s`, write `t = g • s`; then `X_s ∩ X_t` is the basic open of `g` in `X_s`.
  let j : M.nonvanishingLocus s.val ⟶ ⊤ := homOfLE le_top
  have hss : M.nonvanishingLocus s.val ≤ M.nonvanishingLocus (M.presheaf.map j.op s.val) := by
    rw [nonvanishingLocus_map]
    exact le_inf le_rfl le_rfl
  obtain ⟨g, hg⟩ := surjective_smul_of_le_nonvanishingLocus hss (M.presheaf.map j.op t.val)
  rw [← Opens.coe_inf, ← basicOpen_eq_inf_nonvanishingLocus j t.val hss hg]
  exact (s.property.basicOpen g).isCompact

/-- On the structure sheaf `𝒪_X`, regarded as an invertible sheaf, the nonvanishing locus of a
regular function `r` is its basic open set `X_r`. -/
@[simp]
theorem nonvanishingLocus_unit {U : X.Opens} (r : Γ(X, U)) :
    nonvanishingLocus (SheafOfModules.unit X.ringCatSheaf)
      (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from r) = X.basicOpen r := by
  -- The sections of `𝒪_X` over an open `W` are, by definition, the regular functions on `W`,
  -- on which `Γ(X, W)` acts by multiplication and restriction is restriction of functions;
  -- the `show` in the statement and the term `h a` below use this identification.
  let one : Γ(SheafOfModules.unit X.ringCatSheaf, U) := (1 : Γ(X, U))
  have hone : nonvanishingLocus (SheafOfModules.unit X.ringCatSheaf) one = U := by
    refine le_antisymm (nonvanishingLocus_le one) ((le_nonvanishingLocus_iff one (𝟙 U)).mpr ?_)
    intro W j
    have h (a : Γ(X, W)) : a * X.presheaf.map (j ≫ 𝟙 U).op 1 = a := by rw [map_one, mul_one]
    exact ⟨fun a b hab ↦ (h a).symm.trans (hab.trans (h b)), fun a ↦ ⟨a, h a⟩⟩
  convert nonvanishingLocus_smul (M := SheafOfModules.unit X.ringCatSheaf) r one using 1
  · exact congrArg _ (mul_one r).symm
  · rw [hone]
    exact (inf_eq_left.mpr (X.basicOpen_le r)).symm

omit [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] in
private theorem bijective_smul_restrictAppIso_inv_iff {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {U W' : Y.Opens} (k : W' ⟶ U) (s : Γ(M, j ''ᵁ U)) :
    (Function.Bijective fun r : Γ(Y, W') ↦
      r • (M.restrict j).presheaf.map k.op ((M.restrictAppIso j U).inv s)) ↔
    Function.Bijective fun r : Γ(X, j ''ᵁ W') ↦
      r • M.presheaf.map (homOfLE (j.image_mono k.le)).op s := by
  have hM := ConcreteCategory.bijective_of_isIso (M.restrictAppIso j W').hom
  have hj := ConcreteCategory.bijective_of_isIso (j.appIso W').inv
  have hcomp : (M.restrictAppIso j W').hom ∘ (fun r : Γ(Y, W') ↦
      r • (M.restrict j).presheaf.map k.op ((M.restrictAppIso j U).inv s)) =
      (fun r : Γ(X, j ''ᵁ W') ↦
        r • M.presheaf.map (homOfLE (j.image_mono k.le)).op s) ∘ (j.appIso W').inv := by
    funext r; dsimp only [Function.comp_apply]
    rw [smul_restrictAppIso_hom_apply, map_restrictAppIso_hom_apply, Iso.inv_hom_id_apply]
  rw [← Function.Bijective.of_comp_iff' hM, hcomp, Function.Bijective.of_comp_iff _ hj]

/-- Under restriction of an invertible sheaf along an open immersion `j : Y ⟶ X`, the nonvanishing
locus of a section over `j ''ᵁ U` pulls back to `j ⁻¹ᵁ X_s`. -/
@[simp]
theorem nonvanishingLocus_restrictAppIso_inv {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : Y.Opens) (s : Γ(M, j ''ᵁ U)) :
    (M.restrict j).nonvanishingLocus ((M.restrictAppIso j U).inv s) =
      j ⁻¹ᵁ M.nonvanishingLocus s := by
  have hle : j ⁻¹ᵁ M.nonvanishingLocus s ≤ U :=
    (Set.preimage_mono (M.nonvanishingLocus_le s)).trans_eq
      (congrArg SetLike.coe (j.preimage_image_eq U))
  refine le_antisymm ?_ ?_
  · refine (Set.subset_preimage_image j.base _).trans <| Set.preimage_mono <|
      (le_nonvanishingLocus_iff s (homOfLE (j.image_mono
        ((M.restrict j).nonvanishingLocus_le _)))).mpr fun V i ↦ ?_
    obtain ⟨W', hW', rfl⟩ : ∃ W' : Y.Opens,
        W' ≤ (M.restrict j).nonvanishingLocus ((M.restrictAppIso j U).inv s) ∧ j ''ᵁ W' = V := by
      refine ⟨j ⁻¹ᵁ V, (Set.preimage_mono i.le).trans_eq
        (congrArg SetLike.coe (j.preimage_image_eq _)), ?_⟩
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr (i.le.trans (j.image_le_opensRange _))
    have hk := (M.bijective_smul_restrictAppIso_inv_iff j
      (homOfLE hW' ≫ homOfLE ((M.restrict j).nonvanishingLocus_le _)) s).mp
      ((le_nonvanishingLocus_iff _ (homOfLE ((M.restrict j).nonvanishingLocus_le _))).mp
        le_rfl W' (homOfLE hW'))
    rwa [Subsingleton.elim (i ≫ _) (homOfLE _)]
  · refine (le_nonvanishingLocus_iff _ (homOfLE hle)).mpr fun W' k ↦
      (M.bijective_smul_restrictAppIso_inv_iff j (k ≫ homOfLE hle) s).mpr ?_
    have himg : j ''ᵁ (j ⁻¹ᵁ M.nonvanishingLocus s) ≤ M.nonvanishingLocus s := j.image_preimage_le _
    have hk := (le_nonvanishingLocus_iff s (homOfLE (himg.trans (M.nonvanishingLocus_le s)))).mp
      himg (j ''ᵁ W') (homOfLE (j.image_mono k.le))
    rwa [Subsingleton.elim (homOfLE (j.image_mono k.le) ≫ _)
      (homOfLE (j.image_mono (k ≫ homOfLE hle).le))] at hk

private theorem nonvanishingLocus_pullbackSectionsLE_top_of_eq_top {Y : Scheme.{u}} (g : Y ⟶ X)
    {b : Γ(M, ⊤)} (hb : M.nonvanishingLocus b = ⊤) :
    ((pullback g).obj M).nonvanishingLocus
      (g.pullbackSectionsLE M ⊤ ⊤ g.preimage_top.symm.le b) = ⊤ := by
  let φ : (𝟙_ X.Modules : X.Modules) ⟶ M := M.unitHomEquivTop.symm b
  have : IsIso φ :=
    Hom.isIso_iff_isIso_app.mpr fun W ↦ (ConcreteCategory.isIso_iff_bijective _).mpr <| by
      have hfun : (φ.app W : Γ(X, W) → Γ(M, W)) =
          fun r : Γ(X, W) ↦ r • M.presheaf.map (W.leTop ≫ 𝟙 ⊤).op b := funext fun r ↦
        (M.unitHomEquivTop_symm_val_app b W r).trans (by rw [Category.comp_id])
      rw [hfun]; exact (le_nonvanishingLocus_iff b (𝟙 ⊤)).mp hb.ge W W.leTop
  let ψ : (𝟙_ Y.Modules : Y.Modules) ≅ (pullback g).obj M :=
    (pullbackObjUnitIso g).symm ≪≫ (pullback g).mapIso (asIso φ)
  let oneY : Γ(𝟙_ Y.Modules, ⊤) := (1 : Γ(Y, ⊤))
  have hψ : ψ.hom.app ⊤ oneY = g.pullbackSectionsLE M ⊤ ⊤ g.preimage_top.symm.le b := by
    have h2 : ((pullback g).map φ).app ⊤ (g.pullbackSections (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤))) =
        g.pullbackSections M ⊤ b :=
      (Scheme.Hom.pullbackSections_naturality g (𝟙_ X.Modules) ⊤ φ (1 : Γ(X, ⊤))).trans <|
        congrArg (g.pullbackSections M ⊤)
          ((M.unitHomEquivTop_apply φ).symm.trans (M.unitHomEquivTop.apply_symm_apply b))
    exact (ConcreteCategory.comp_apply _ _ oneY).trans <|
      (congrArg _ (Scheme.Hom.pullbackObjUnitIso_inv_app_one g)).trans <|
        h2.trans (Scheme.Hom.pullbackSectionsLE_self g M ⊤ b).symm
  rw [← hψ, nonvanishingLocus_hom_app ψ]
  exact (nonvanishingLocus_unit (1 : Γ(Y, ⊤))).trans Y.basicOpen_one

private theorem nonvanishingLocus_pullbackSections_ι (V : X.Opens) (b : Γ(M, V)) :
    ((pullback V.ι).obj M).nonvanishingLocus (V.ι.pullbackSections M V b) =
      V.ι ⁻¹ᵁ M.nonvanishingLocus b := by
  rw [Scheme.Hom.pullbackSections_of_isOpenImmersion,
    nonvanishingLocus_hom_app ((restrictFunctorIsoPullback V.ι).app M),
    nonvanishingLocus_restrictAppIso_inv, nonvanishingLocus_map,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem,
    inf_eq_right.mpr (M.nonvanishingLocus_le b)]

private theorem le_nonvanishingLocus_pullbackSections_of_le {Y : Scheme.{u}} (g : Y ⟶ X)
    {W : X.Opens} {b : Γ(M, W)} (hb : W ≤ M.nonvanishingLocus b) :
    g ⁻¹ᵁ W ≤ ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M W b) := by
  let g' : (g ⁻¹ᵁ W).toScheme ⟶ W.toScheme := g.resLE W (g ⁻¹ᵁ W) le_rfl
  have hWtop : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := W.ι_preimage_self.symm.le
  have hgWtop : (⊤ : (g ⁻¹ᵁ W).toScheme.Opens) ≤ (g ⁻¹ᵁ W).ι ⁻¹ᵁ (g ⁻¹ᵁ W) :=
    (g ⁻¹ᵁ W).ι_preimage_self.symm.le
  let b₀ : Γ((pullback W.ι).obj M, ⊤) := W.ι.pullbackSectionsLE M W ⊤ hWtop b
  have hb₀ : ((pullback W.ι).obj M).nonvanishingLocus b₀ = ⊤ := by
    dsimp only [b₀]; rw [Scheme.Hom.pullbackSectionsLE_apply, nonvanishingLocus_map,
      nonvanishingLocus_pullbackSections_ι, top_inf_eq, eq_top_iff]
    exact fun ⟨x, hxW⟩ _ ↦ hb hxW
  let e : (pullback g').obj ((pullback W.ι).obj M) ≅
      (pullback (g ⁻¹ᵁ W).ι).obj ((pullback g).obj M) :=
    (pullbackComp g' W.ι).app M ≪≫ (pullbackCongr (g.resLE_comp_ι le_rfl)).app M ≪≫
      ((pullbackComp (g ⁻¹ᵁ W).ι g).app M).symm
  have he : e.hom.app ⊤ (g'.pullbackSectionsLE ((pullback W.ι).obj M) ⊤ ⊤
      g'.preimage_top.symm.le b₀) = (g ⁻¹ᵁ W).ι.pullbackSectionsLE ((pullback g).obj M)
      (g ⁻¹ᵁ W) ⊤ hgWtop (g.pullbackSections M W b) := by
    simp only [e, b₀, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Hom.comp_app]
    have s1 := Scheme.Hom.pullbackSectionsLE_comp_hom W.ι M W g' ⊤ hWtop (W := ⊤)
      g'.preimage_top.symm.le b
    have s2 := Scheme.Hom.pullbackSectionsLE_congr (g' ≫ W.ι) M W ⊤
      (g'.preimage_top.symm.le.trans (Set.preimage_mono hWtop)) (g.resLE_comp_ι le_rfl) b
    have s3 := (Scheme.Hom.pullbackSectionsLE_comp g M W (g ⁻¹ᵁ W).ι (g ⁻¹ᵁ W) le_rfl
      (W := ⊤) hgWtop b).trans <| congrArg
        ((g ⁻¹ᵁ W).ι.pullbackSectionsLE ((pullback g).obj M) (g ⁻¹ᵁ W) ⊤ hgWtop)
        (Scheme.Hom.pullbackSectionsLE_self g M W b)
    exact (ConcreteCategory.comp_apply _ _ _).trans <| (congrArg _ s1).trans <|
      (ConcreteCategory.comp_apply _ _ _).trans <| (congrArg _ s2).trans s3
  have htop : ((pullback (g ⁻¹ᵁ W).ι).obj ((pullback g).obj M)).nonvanishingLocus
      ((g ⁻¹ᵁ W).ι.pullbackSectionsLE ((pullback g).obj M) (g ⁻¹ᵁ W) ⊤ hgWtop
        (g.pullbackSections M W b)) = ⊤ := by
    rw [← he, nonvanishingLocus_hom_app e,
      nonvanishingLocus_pullbackSectionsLE_top_of_eq_top g' hb₀]
  rw [Scheme.Hom.pullbackSectionsLE_apply, nonvanishingLocus_map,
    nonvanishingLocus_pullbackSections_ι, top_inf_eq] at htop
  exact fun y hy ↦ (eq_top_iff.mp htop (Opens.mem_top ⟨y, hy⟩) : y ∈ _)

/-- **Pullback commutes with nonvanishing loci.** For any morphism of schemes `g : Y ⟶ X` and
section `s` of an invertible sheaf `M` over `U`, the nonvanishing locus of `g^* s` is the preimage
`g ⁻¹ᵁ X_s`. -/
@[simp]
theorem nonvanishingLocus_pullbackSections {Y : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens}
    (s : Γ(M, U)) :
    ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M U s) =
      g ⁻¹ᵁ M.nonvanishingLocus s := by
  ext y; by_cases hyU : y ∈ g ⁻¹ᵁ U
  · obtain ⟨V, t, hgyV⟩ := exists_mem_trivialization M (g.base y)
    let i : U ⊓ V ⟶ V := homOfLE inf_le_right; let j : U ⊓ V ⟶ U := homOfLE inf_le_left
    let b : Γ(M, U ⊓ V) := M.presheaf.map i.op (trivializationGenerator M t)
    let r : Γ(X, U ⊓ V) := trivializationCoordinate M t i (M.presheaf.map j.op s)
    have hb : U ⊓ V ≤ M.nonvanishingLocus b := by
      rw [nonvanishingLocus_map, nonvanishingLocus_trivializationGenerator]
      exact le_inf le_rfl inf_le_right
    have hs : M.presheaf.map j.op s = r • b :=
      eq_trivializationCoordinate_smul_map_trivializationGenerator M t i _
    have hLHS : y ∈ g ⁻¹ᵁ (U ⊓ V) ⊓ ((pullback g).obj M).nonvanishingLocus
        (g.pullbackSections M U s) ↔ y ∈ Y.basicOpen (g.app (U ⊓ V) r) := by
      rw [← nonvanishingLocus_map ((Opens.map g.base).map j) (g.pullbackSections M U s),
        Scheme.Hom.pullbackSections_restrict, hs, map_smulₛₗ, nonvanishingLocus_smul,
        inf_eq_left.mpr
          ((Y.basicOpen_le _).trans (M.le_nonvanishingLocus_pullbackSections_of_le g hb))]
    have hRHS : y ∈ g ⁻¹ᵁ (U ⊓ V) ⊓ g ⁻¹ᵁ M.nonvanishingLocus s ↔
        y ∈ Y.basicOpen (g.app (U ⊓ V) r) := by
      rw [← Scheme.Hom.preimage_inf, ← nonvanishingLocus_map, hs, nonvanishingLocus_smul,
        inf_eq_left.mpr ((X.basicOpen_le r).trans hb), Scheme.preimage_basicOpen]
    exact ⟨fun h ↦ (hRHS.mpr (hLHS.mp ⟨⟨hyU, hgyV⟩, h⟩)).2,
      fun h ↦ (hLHS.mpr (hRHS.mp ⟨⟨hyU, hgyV⟩, h⟩)).2⟩
  · exact iff_of_false (fun h ↦ hyU (((pullback g).obj M).nonvanishingLocus_le _ h))
      (fun h ↦ hyU (M.nonvanishingLocus_le s h))

/-- The nonvanishing locus of a section pulled back along `g` and restricted to `V ≤ g ⁻¹ᵁ U` is
`V ⊓ g ⁻¹ᵁ X_s`. -/
@[simp]
theorem nonvanishingLocus_pullbackSectionsLE {Y : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens}
    (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((pullback g).obj M).nonvanishingLocus (g.pullbackSectionsLE M U V hV s) =
      V ⊓ g ⁻¹ᵁ M.nonvanishingLocus s := by
  rw [Scheme.Hom.pullbackSectionsLE_apply, nonvanishingLocus_map,
    nonvanishingLocus_pullbackSections]

/-- A quasi-compact open `U` is covered by finitely many affine opens `V i ≤ U`, each carrying a
section `e i` of `M` that vanishes nowhere on `V i`. -/
theorem exists_finite_affine_cover_le_nonvanishingLocus {U : X.Opens} (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens) (e : ∀ i, Γ(M, V i)),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ U) ∧ (∀ i, V i ≤ M.nonvanishingLocus (e i)) ∧
        U ≤ ⨆ i, V i := by
  have H (x : U) : ∃ (A : X.Opens) (e : Γ(M, A)), IsAffineOpen A ∧ (x : X) ∈ A ∧ A ≤ U ∧
      A ≤ M.nonvanishingLocus e := by
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show (x : X) ∈ ((U ⊓ V : X.Opens) : Set X) from ⟨x.property, hxV⟩) (U ⊓ V).isOpen
    refine ⟨A, M.presheaf.map (homOfLE fun y hy ↦ (hAUV hy).2).op (trivializationGenerator M t),
      hA, hxA, fun y hy ↦ (hAUV hy).1, ?_⟩
    rw [nonvanishingLocus_map, nonvanishingLocus_trivializationGenerator]
    exact le_inf le_rfl (fun y hy ↦ (hAUV hy).2)
  choose A e hA hxA hAU hAe using H
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (A x : Set X)) (fun x ↦ (A x).isOpen)
    fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩
  refine ⟨t, inferInstance, fun i ↦ A i, fun i ↦ e i, fun i ↦ hA i, fun i ↦ hAU i, fun i ↦ hAe i,
    fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx); exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

/-- If `U` is a retrocompact open of `X`, the nonvanishing locus `X_s` of any section `s` of an
invertible sheaf `M` over `U` is retrocompact in `X`. -/
theorem isRetrocompact_nonvanishingLocus_of_isRetrocompact {U : X.Opens}
    (hU : IsRetrocompact (X := X) (U : Set X)) (s : Γ(M, U)) :
    IsRetrocompact (X := X) (M.nonvanishingLocus s) := by
  intro W hWc hWo
  obtain ⟨ι, _, V, e, hVa, hVUW, hVe, hUWV⟩ :=
    M.exists_finite_affine_cover_le_nonvanishingLocus (U := U ⊓ ⟨W, hWo⟩) (hU hWc hWo)
  choose f hf using fun i ↦ surjective_smul_of_le_nonvanishingLocus (hVe i)
    (M.presheaf.map (homOfLE ((hVUW i).trans inf_le_left)).op s)
  beta_reduce at hf
  have hD (i : ι) : X.basicOpen (f i) = V i ⊓ M.nonvanishingLocus s :=
    M.basicOpen_eq_inf_nonvanishingLocus (homOfLE ((hVUW i).trans inf_le_left)) s (hVe i) (hf i)
  have heq : (M.nonvanishingLocus s : Set X) ∩ W = ⋃ i : ι, (X.basicOpen (f i) : Set X) := by
    ext x; simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iUnion, hD, Opens.mem_inf]
    refine ⟨fun ⟨hxs, hxW⟩ ↦ ?_, fun ⟨i, hxi, hxs⟩ ↦ ⟨hxs, (hVUW i hxi).2⟩⟩
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hUWV ⟨M.nonvanishingLocus_le s hxs, hxW⟩)
    exact ⟨i, hxi, hxs⟩
  rw [heq]; exact isCompact_iUnion fun i ↦ ((hVa i).basicOpen (f i)).isCompact

/-- The nonvanishing locus `X_s` of a global section `s` of an invertible sheaf `M` is retrocompact
in `X`. -/
theorem isRetrocompact_nonvanishingLocus (s : Γ(M, ⊤)) :
    IsRetrocompact (X := X) (M.nonvanishingLocus s) :=
  M.isRetrocompact_nonvanishingLocus_of_isRetrocompact
    (fun _ hWc _ ↦ by simpa only [Opens.coe_top, Set.univ_inter] using hWc) s

/-- **Nonvanishing loci in an affine open are affine.** If `U` is an affine open of `X`, then the
nonvanishing locus `X_s` of every section `s` of an invertible sheaf over `U` is affine. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.nonvanishingLocus {U : X.Opens}
    (hU : IsAffineOpen U) (s : Γ(M, U)) : IsAffineOpen (M.nonvanishingLocus s) := by
  -- Cover `U` by basic opens `D(f)` on which `M` is trivial; on each of them `X_s` is the basic
  -- open of the coordinate of `s`, so affine.
  have H (x : U) : ∃ f : Γ(X, U), (x : X) ∈ X.basicOpen f ∧
      IsAffineOpen (M.nonvanishingLocus s ⊓ X.basicOpen f) := by
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ x.property
    refine ⟨f, hxf, ?_⟩
    rw [inf_comm, ← nonvanishingLocus_map (homOfLE (X.basicOpen_le f)),
      nonvanishingLocus_eq_basicOpen t (homOfLE hfV)]
    exact (hU.basicOpen f).basicOpen _
  choose f hxf hf using H
  -- The restrictions of the functions `f` to `X_s` generate the unit ideal, and their basic opens
  -- are the affine opens `X_s ∩ D(f)`.
  let j : M.nonvanishingLocus s ⟶ U := homOfLE (M.nonvanishingLocus_le s)
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (X.presheaf.map j.op '' Set.range f) ?_ ?_
  · rw [← Ideal.map_span, (hU.self_le_iSup_basicOpen_iff (s := Set.range f)).mp, Ideal.map_top]
    exact fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, hxf ⟨x, hx⟩⟩
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [X.basicOpen_res]
    exact hf x

variable (M) in
/-- **Sections over an affine open generate the stalks.** Every point `x` of an affine open `U`
lies in the nonvanishing locus of some section of an invertible sheaf over `U`. -/
theorem exists_mem_nonvanishingLocus_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) : ∃ s : Γ(M, U), x ∈ M.nonvanishingLocus s := by
  have : M.IsQuasicoherent :=
    TauCeti.AlgebraicGeometry.InvertibleSheaf.isQuasicoherent_obj ⟨M, ‹_›⟩
  obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  -- A power of `f` times the basis section over `D(f) ⊆ V` extends to a section `s` over `U`,
  -- so `s` vanishes nowhere on `D(f)`.
  obtain ⟨n, s, hs⟩ := M.exists_pow_smul_eq_map hU f rfl (X.basicOpen_le f)
    (M.presheaf.map (homOfLE hfV).op (trivializationGenerator M t))
  refine ⟨s, (inf_le_right : X.basicOpen f ⊓ _ ≤ _) ?_⟩
  rw [← nonvanishingLocus_map (homOfLE (X.basicOpen_le f)), ← hs,
    nonvanishingLocus_smul, nonvanishingLocus_map,
    nonvanishingLocus_trivializationGenerator, ← map_pow, X.basicOpen_res]
  refine ⟨⟨hxf, ?_⟩, hxf, hxV⟩
  rw [SetLike.mem_coe, X.mem_basicOpen _ _ hx, map_pow]
  exact ((X.mem_basicOpen _ _ hx).mp hxf).pow n

end AlgebraicGeometry.Scheme.Modules
