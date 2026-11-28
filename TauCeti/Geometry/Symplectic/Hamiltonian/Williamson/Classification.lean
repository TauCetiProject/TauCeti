/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Mixed
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Regular
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Type

/-!
# The Williamson type of a nondegenerate family of quadratic forms

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic
forms on `V` is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the
Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra of `sp(V, ω)`. Williamson's
classification
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks`) says
that, after a linear symplectic change of coordinates, such a family spans the same space as
`k_e` elliptic blocks `(xₖ² + yₖ²) / 2`, `k_h` hyperbolic blocks `xₖ yₖ` and `k_f` focus-focus
pairs `x y + x' y'`, `x y' - x' y`, on disjoint symplectic coordinate planes
(`TauCeti.SymplecticForm.williamsonBlocks`). This file packages the numbers `(k_e, k_h, k_f)` as
the **Williamson type** of the family.

The family `Q` has type `(k_e, k_h, k_f)` (`TauCeti.SymplecticForm.HasWilliamsonType`) when its
span is the span of the Williamson blocks of a Darboux basis with `k_e + k_h + 2 k_f` planes, of
which `k_e` carry elliptic blocks, the other `k_h` of the first `k_e + k_h` planes carry hyperbolic
blocks, and the last `2 k_f` carry focus-focus pairs. Then:

* every nondegenerate family has a type
  (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.exists_hasWilliamsonType`);
* the type is unique (`TauCeti.SymplecticForm.HasWilliamsonType.unique`), by the invariance of the
  numbers of blocks
  (`IsDarbouxBasis.eq_and_eq_and_card_eq_of_span_williamsonBlocks_eq`);
* it fills the dimension: `2 (k_e + k_h + 2 k_f) = dim V`
  (`TauCeti.SymplecticForm.HasWilliamsonType.two_mul_add_add_eq_finrank`);
* it depends only on the span of the family
  (`TauCeti.SymplecticForm.hasWilliamsonType_iff_of_span_eq`) and is invariant under linear
  symplectomorphisms (`TauCeti.SymplecticForm.hasWilliamsonType_comp_iff`), in particular under
  the reduction by the whole space
  (`TauCeti.SymplecticForm.hasWilliamsonType_reduction_iff_of_eq_top`);
* the Williamson blocks of a Darboux basis with `m + 2 f` planes and elliptic planes `u` have type
  `(|u|, m - |u|, f)` (`TauCeti.SymplecticForm.IsDarbouxBasis.hasWilliamsonType_williamsonBlocks`);
  in particular the elliptic blocks of a Darboux basis with `n` planes have type `(n, 0, 0)`
  (`TauCeti.SymplecticForm.IsDarbouxBasis.hasWilliamsonType_elliptic`).

The type of a nondegenerate singular point of an integrable system is the type of its family of
transversal Hessians, in `TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint.Williamson`.

## Main definitions

* `TauCeti.SymplecticForm.HasWilliamsonType ω Q kₑ kₕ k_f`: the family `Q` has Williamson type
  `(kₑ, kₕ, k_f)`.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* E. Miranda and N. T. Zung, *Equivariant normal form for nondegenerate singular orbits of
  integrable Hamiltonian systems*, Annales scientifiques de l'École Normale Supérieure 37 (2004),
  819–839, Section 2.
-/

public section

noncomputable section

open Module

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {ι κ : Type*} {kₑ kₕ k_f : ℕ}

variable (ω : SymplecticForm V) in
/-- A family `Q` of quadratic forms on `(V, ω)` has **Williamson type** `(kₑ, kₕ, k_f)` when its
span is the span of the Williamson blocks `williamsonBlocks b u` of a Darboux basis `b` with
`m + 2 k_f` planes, `m = kₑ + kₕ`, and a set `u` of `kₑ` planes among the first `m`: `kₑ` elliptic
blocks `(xₖ² + yₖ²) / 2`, `kₕ` hyperbolic blocks `xₖ yₖ` and `k_f` focus-focus pairs. -/
def HasWilliamsonType (Q : ι → QuadraticForm ℝ V) (kₑ kₕ k_f : ℕ) : Prop :=
  ∃ (m : ℕ) (b : Basis (Fin (m + k_f * 2) × Fin 2) ℝ V) (u : Finset (Fin m)),
    ω.IsDarbouxBasis b ∧ u.card = kₑ ∧ m = kₑ + kₕ ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b u))

variable {ω : SymplecticForm V}

/-- Unfolding `HasWilliamsonType`. -/
theorem hasWilliamsonType_iff (Q : ι → QuadraticForm ℝ V) :
    ω.HasWilliamsonType Q kₑ kₕ k_f ↔
      ∃ (m : ℕ) (b : Basis (Fin (m + k_f * 2) × Fin 2) ℝ V) (u : Finset (Fin m)),
        ω.IsDarbouxBasis b ∧ u.card = kₑ ∧ m = kₑ + kₕ ∧
          Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b u)) :=
  Iff.rfl

/-- The Williamson type of a family depends only on the span of the family. -/
theorem hasWilliamsonType_iff_of_span_eq {Q : ι → QuadraticForm ℝ V} {Q' : κ → QuadraticForm ℝ V}
    (h : Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range Q')) :
    ω.HasWilliamsonType Q kₑ kₕ k_f ↔ ω.HasWilliamsonType Q' kₑ kₕ k_f := by
  simp only [HasWilliamsonType, h]

/-- **The type of a Williamson normal form.** The Williamson blocks of a Darboux basis with
`m + 2 f` planes and a set `u` of elliptic planes among the first `m` have Williamson type
`(|u|, m - |u|, f)`. -/
theorem IsDarbouxBasis.hasWilliamsonType_williamsonBlocks {m f : ℕ}
    {b : Basis (Fin (m + f * 2) × Fin 2) ℝ V} (hb : ω.IsDarbouxBasis b) (u : Finset (Fin m)) :
    ω.HasWilliamsonType (williamsonBlocks b u) u.card (m - u.card) f :=
  ⟨m, b, u, hb, rfl, by have := (Finset.card_le_univ u).trans_eq (Fintype.card_fin m); omega, rfl⟩

/-- **The elliptic type.** The elliptic blocks `(xₖ² + yₖ²) / 2` of a Darboux basis with `n`
planes have Williamson type `(n, 0, 0)`. -/
theorem IsDarbouxBasis.hasWilliamsonType_elliptic {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V}
    (hb : ω.IsDarbouxBasis b) : ω.HasWilliamsonType (elliptic b) n 0 0 := by
  have h := hb.hasWilliamsonType_williamsonBlocks (f := 0) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin, Nat.sub_self] at h
  refine (hasWilliamsonType_iff_of_span_eq (congrArg _ ?_)).1 h
  -- Every plane carries its elliptic block, and there are no focus-focus pairs.
  have hk (k : Fin n) : williamsonBlocks (f := 0) b Finset.univ (.inl k) = elliptic b k := by
    have hmem : Fin.castAdd (0 * 2) k ∈ Finset.univ.map (Fin.castAddEmb (0 * 2)) :=
      Finset.mem_map_of_mem _ (Finset.mem_univ k)
    rw [williamsonBlocks_inl, ellipticHyperbolic_of_mem hmem]
    simp
  ext R
  refine ⟨?_, fun ⟨k, hR⟩ ↦ ⟨.inl k, hR ▸ hk k⟩⟩
  rintro ⟨k | ⟨j, -⟩, rfl⟩
  · exact ⟨k, (hk k).symm⟩
  · exact j.elim0

/-- **Uniqueness of the Williamson type.** A family has at most one Williamson type: the numbers of
elliptic, hyperbolic and focus-focus blocks of a normal form are determined by its span. -/
theorem HasWilliamsonType.unique [FiniteDimensional ℝ V] {Q : ι → QuadraticForm ℝ V}
    {kₑ' kₕ' k_f' : ℕ} (h : ω.HasWilliamsonType Q kₑ kₕ k_f)
    (h' : ω.HasWilliamsonType Q kₑ' kₕ' k_f') : kₑ = kₑ' ∧ kₕ = kₕ' ∧ k_f = k_f' := by
  obtain ⟨m, b, u, hb, rfl, hm, hspan⟩ := h
  obtain ⟨m', b', u', hb', rfl, hm', hspan'⟩ := h'
  obtain ⟨hmm, hff, huu⟩ :=
    hb.eq_and_eq_and_card_eq_of_span_williamsonBlocks_eq hb' (hspan.symm.trans hspan')
  exact ⟨huu, by omega, hff⟩

/-- **The Williamson type fills the dimension.** A family of Williamson type `(kₑ, kₕ, k_f)` lives
on a space of dimension `2 (kₑ + kₕ + 2 k_f)`: the normal form has `kₑ + kₕ` planes carrying an
elliptic or a hyperbolic block and `k_f` pairs of planes carrying a focus-focus pair. -/
theorem HasWilliamsonType.two_mul_add_add_eq_finrank {Q : ι → QuadraticForm ℝ V}
    (h : ω.HasWilliamsonType Q kₑ kₕ k_f) :
    2 * (kₑ + kₕ + 2 * k_f) = finrank ℝ V := by
  obtain ⟨m, b, u, -, -, rfl, -⟩ := h
  rw [finrank_eq_card_basis b, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

/-- **Existence of the Williamson type.** Every nondegenerate family of quadratic forms, one whose
Hamiltonian endomorphisms generate a Cartan subalgebra of `sp(V, ω)`, has a Williamson type. -/
theorem IsNondegenerateQuadraticFamily.exists_hasWilliamsonType [FiniteDimensional ℝ V]
    {Q : ι → QuadraticForm ℝ V} (h : ω.IsNondegenerateQuadraticFamily Q) :
    ∃ kₑ kₕ k_f, ω.HasWilliamsonType Q kₑ kₕ k_f := by
  obtain ⟨m, f, b, u, hb, hspan⟩ := h.exists_isDarbouxBasis_span_eq_span_williamsonBlocks
  exact ⟨_, _, _, (hasWilliamsonType_iff_of_span_eq hspan).2
    (hb.hasWilliamsonType_williamsonBlocks u)⟩

/-- Pulling a family of Williamson type `(kₑ, kₕ, k_f)` on `(W, ω')` back along a linear
symplectomorphism `e : (V, ω) → (W, ω')` gives a family of the same type: the Darboux basis is
transported along `e⁻¹`, and its Williamson blocks are those of the original basis composed with
`e`. -/
private theorem HasWilliamsonType.comp {ω' : SymplecticForm W} {e : V ≃ₗ[ℝ] W}
    (he : IsSymplectomorphism ω ω' e) {Q : ι → QuadraticForm ℝ W}
    (h : ω'.HasWilliamsonType Q kₑ kₕ k_f) :
    ω.HasWilliamsonType (fun i ↦ (Q i).comp (e : V →ₗ[ℝ] W)) kₑ kₕ k_f := by
  obtain ⟨m, b, u, hb, hu, hm, hspan⟩ := h
  refine ⟨m, b.map e.symm, u, hb.map he.symm, hu, hm, ?_⟩
  have hblocks : (fun k ↦ (williamsonBlocks b u k).comp (e : V →ₗ[ℝ] W)) =
      williamsonBlocks (b.map e.symm) u := by
    funext k
    have hbe : (b.map e.symm).map e = b := Basis.eq_of_apply_eq fun _ ↦ by simp
    have := williamsonBlocks_map (b.map e.symm) u e k
    rwa [hbe] at this
  -- Composition with `e` is a linear map on quadratic forms, so it maps spans to spans.
  let c : QuadraticForm ℝ W →ₗ[ℝ] QuadraticForm ℝ V :=
    { toFun := fun R ↦ R.comp (e : V →ₗ[ℝ] W)
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  -- The coercion of `c` is its `toFun` field by definition.
  have hc (R : QuadraticForm ℝ W) : R.comp (e : V →ₗ[ℝ] W) = c R := rfl
  simp only [← hblocks, hc, Set.range_comp', ← Submodule.map_span, hspan]

/-- **Invariance of the Williamson type under linear symplectomorphisms.** If `e : V ≃ W` carries
`ω` to `ω'`, a family `Q` of quadratic forms on `W` has Williamson type `(kₑ, kₕ, k_f)` for `ω'`
exactly when its pullback `Q ∘ e` has this type for `ω`. -/
theorem hasWilliamsonType_comp_iff {ω' : SymplecticForm W} {e : V ≃ₗ[ℝ] W}
    (he : IsSymplectomorphism ω ω' e) (Q : ι → QuadraticForm ℝ W) :
    ω.HasWilliamsonType (fun i ↦ (Q i).comp (e : V →ₗ[ℝ] W)) kₑ kₕ k_f ↔
      ω'.HasWilliamsonType Q kₑ kₕ k_f := by
  refine ⟨fun h ↦ ?_, HasWilliamsonType.comp he⟩
  have hQ : (fun i ↦ ((Q i).comp (e : V →ₗ[ℝ] W)).comp (e.symm : W →ₗ[ℝ] V)) = Q := by
    funext i
    ext w
    simp
  simpa only [hQ] using h.comp he.symm

/-- Over the whole space, the Williamson type of a family of reduced quadratic forms is the
Williamson type of the original family. -/
theorem hasWilliamsonType_reduction_iff_of_eq_top {U : Submodule ℝ V}
    (hU : U = ⊤) (Q : ι → QuadraticForm ℝ V)
    (hQ : ∀ i, ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U, QuadraticMap.polar (Q i) w u = 0) :
    (ω.reduction U).HasWilliamsonType (fun i ↦ ω.reducedQuadraticForm U (Q i) (hQ i)) kₑ kₕ k_f ↔
      ω.HasWilliamsonType Q kₑ kₕ k_f := by
  subst hU
  rw [← hasWilliamsonType_comp_iff ω.isSymplectomorphism_reducedSpaceTopEquiv]
  congr! with i
  ext v
  simp

end TauCeti.SymplecticForm
