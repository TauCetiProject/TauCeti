/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.RelativeCube

/-!
# Relative homotopy sets of preimage pairs under a Serre fibration

Let `p : E → B` be a Serre fibration, `A ⊆ B` and `e ∈ p⁻¹(A)`. Then `p` induces a bijection

`π_{n+1}(E, p⁻¹(A), e) → π_{n+1}(B, A, p e)`

of relative homotopy sets for every `n ≥ 0`
(`TauCeti.TopCat.relHomotopyGroup_map_bijective_of_mem_serreFibrations`). For `A = {b}` this is
Hatcher's Theorem 4.41, `π_{n+1}(E, F, e) ≅ π_{n+1}(B, b, b)` for the fibre `F = p⁻¹(b)`, through
which the exact sequence of the pair `(E, F)` becomes the homotopy exact sequence of the fibration.

Both halves are proved by relative cube lifting:

* **surjectivity**: a relative cube `q : I × Iⁿ → B` of `(B, A, p e)` is constant at `p e` on the
  face `{1} × Iⁿ` and on the sides. Lifting it from the constant map at `e` there gives a cube of
  `E` that is constant at `e` there, and whose free face `{0} × Iⁿ` lies over `A`, that is, in
  `p⁻¹(A)` (`TauCeti.TopCat.relHomotopyGroup_map_surjective_of_mem_serreFibrations`);
* **injectivity**: if the images of two relative cubes `γ₀`, `γ₁` of `(E, p⁻¹(A), e)` are
  homotopic through relative cubes, the homotopy lifts to one from `γ₀` to `γ₁` that stays at `e`
  on the face `{1} × Iⁿ` and on the sides
  (`TauCeti.TopCat.exists_lift_homotopy_of_mem_serreFibrations`). On the free face it lies over
  `A`, so it is a homotopy through relative cubes of `(E, p⁻¹(A), e)`
  (`TauCeti.TopCat.relHomotopyGroup_map_injective_of_mem_serreFibrations`).

So the pair `(E, p⁻¹(A))` is exactly as highly connected as the pair `(B, A)`
(`TauCeti.TopCat.subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations`). For the skeleta
`Xⁱ ⊆ Xⁱ⁺¹` of a CW complex this says that the pairs `(p⁻¹(Xⁱ⁺¹), p⁻¹(Xⁱ))` of the skeletal
filtration of a fibration over `X` are `i`-connected, which is what places the first page of its
spectral sequence in nonnegative fibre degrees. Likewise, if every point of `B` is joined by a path
to a point of `A`, every point of `E` is joined by a path to a point of `p⁻¹(A)`
(`TauCeti.TopCat.exists_joined_preimage_of_mem_serreFibrations`).

## Main definitions

* `TauCeti.TopCat.preimageBasedPairHom`: `p` as a morphism of based pairs
  `(E, p⁻¹(A), e) ⟶ (B, A, p e)`.

## Main results

* `TauCeti.TopCat.relHomotopyGroup_map_bijective_of_mem_serreFibrations`: a Serre fibration
  induces bijections `π_{n+1}(E, p⁻¹(A), e) → π_{n+1}(B, A, p e)`.
* `TauCeti.TopCat.subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations`:
  `π_{n+1}(E, p⁻¹(A), e)` is trivial when `π_{n+1}(B, A, p e)` is.
* `TauCeti.TopCat.exists_joined_preimage_of_mem_serreFibrations`: points of `E` are joined to
  `p⁻¹(A)` when points of `B` are joined to `A`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Theorem 4.41 and its proof (relative homotopy groups of a fibration and of its
  base).
-/

public section

universe u v

open CategoryTheory Set unitInterval
open scoped Topology Topology.Homotopy

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

variable (p) in
/-- The map `p : E ⟶ B` as a morphism of based pairs `(E, p⁻¹(A), e) ⟶ (B, A, p e)`. -/
def preimageBasedPairHom (A : Set B) (e : p ⁻¹' A) :
    (⟨TopPair.ofSubset (p ⁻¹' A), e⟩ : BasedTopPair) ⟶ ⟨TopPair.ofSubset A, ⟨p e, e.property⟩⟩ :=
  ⟨TopPair.ofSubsetMap p fun _ h ↦ h, Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)⟩

@[simp]
theorem preimageBasedPairHom_fst_apply (A : Set B) (e : p ⁻¹' A)
    (x : (TopPair.ofSubset (p ⁻¹' A)).fst) :
    TopPair.Hom.fst (preimageBasedPairHom p A e).toTopPairHom x = p x :=
  TopPair.ofSubsetMap_fst_apply p _ x

@[simp]
theorem preimageBasedPairHom_snd_apply (A : Set B) (e : p ⁻¹' A)
    (x : (TopPair.ofSubset (p ⁻¹' A)).snd) :
    (TopPair.Hom.snd (preimageBasedPairHom p A e).toTopPairHom x).val = p x.val :=
  TopPair.ofSubsetMap_snd_apply p _ x

/-- **A Serre fibration induces surjections of relative homotopy sets.** For a Serre fibration
`p : E ⟶ B`, `A ⊆ B` and `e ∈ p⁻¹(A)`, every class of `π_{n+1}(B, A, p e)` is the image of a class
of `π_{n+1}(E, p⁻¹(A), e)`, where `n` is the cardinality of `N`. -/
theorem relHomotopyGroup_map_surjective_of_mem_serreFibrations (hp : serreFibrations p)
    {N : Type v} [Finite N] (A : Set B) (e : p ⁻¹' A) :
    Function.Surjective (RelHomotopyGroup.map (N := N) (preimageBasedPairHom p A e)) := by
  intro a
  obtain ⟨q, rfl⟩ := RelHomotopyGroup.mk_surjective a
  -- Lift `q`, with its time reversed, from the constant map at `e` on the face `{1} × Iᴺ` and
  -- the sides.
  obtain ⟨G, hG, hGf⟩ := exists_lift_openBox_of_mem_serreFibrations hp N
    (ContinuousMap.const _ (e : E)) (q.val.comp ⟨fun y ↦ (σ y.1, y.2), by fun_prop⟩) <| by
      rintro ⟨⟨s, t⟩, hst⟩
      rcases mem_cylinderExtensionDomain_iff.1 hst with h | h
      · obtain rfl : s = 0 := h
        exact (RelGenLoop.mem_iff.1 q.property).2 _ t (.inl symm_zero) |>.symm
      · exact (RelGenLoop.apply_of_mem_boundary q _ h).symm
  have hpG (y : I × (I^N)) : p (G y) = q.val (σ y.1, y.2) := congrFun hG y
  -- Its free face lies over `A`, so it is a relative cube of `(E, p⁻¹(A), e)` over `q`.
  refine ⟨RelHomotopyGroup.mk ⟨G.comp ⟨fun y ↦ (σ y.1, y.2), by fun_prop⟩,
    RelGenLoop.mem_iff.2 ⟨fun t ↦ ⟨⟨G (σ 0, t), ?_⟩, rfl⟩, fun s t h ↦ hGf ⟨(σ s, t), ?_⟩⟩⟩, ?_⟩
  · have hq := RelGenLoop.apply_zero_mem_range q t
    rw [TopPair.range_ofSubset_map] at hq
    rwa [mem_preimage, hpG, symm_symm]
  · exact mem_cylinderExtensionDomain_iff.2 (h.imp_left fun h ↦ by rw [h, symm_one])
  · rw [RelHomotopyGroup.map_mk]
    refine congrArg RelHomotopyGroup.mk (RelGenLoop.ext fun y ↦ ?_)
    refine (RelGenLoop.map_apply _ _ y).trans ((preimageBasedPairHom_fst_apply A e _).trans ?_)
    -- The relative cube built from `G` evaluates as the composite of `G` with the time reversal.
    exact (hpG _).trans (congrArg q.val (Prod.ext (symm_symm _) rfl))

/-- **A Serre fibration induces injections of relative homotopy sets.** For a Serre fibration
`p : E ⟶ B`, `A ⊆ B` and `e ∈ p⁻¹(A)`, two classes of `π_{n+1}(E, p⁻¹(A), e)` with the same image
in `π_{n+1}(B, A, p e)` are equal, where `n` is the cardinality of `N`. -/
theorem relHomotopyGroup_map_injective_of_mem_serreFibrations (hp : serreFibrations p)
    {N : Type v} [Finite N] (A : Set B) (e : p ⁻¹' A) :
    Function.Injective (RelHomotopyGroup.map (N := N) (preimageBasedPairHom p A e)) := by
  intro a b hab
  obtain ⟨γ₀, rfl⟩ := RelHomotopyGroup.mk_surjective a
  obtain ⟨γ₁, rfl⟩ := RelHomotopyGroup.mk_surjective b
  rw [RelHomotopyGroup.map_mk, RelHomotopyGroup.map_mk] at hab
  obtain ⟨F⟩ := RelGenLoop.homotopic_iff.1 (RelHomotopyGroup.mk_eq_mk.1 hab)
  have hmap (γ : RelGenLoop N ⟨TopPair.ofSubset (p ⁻¹' A), e⟩) (y : I × (I^N)) :
      (RelGenLoop.map (preimageBasedPairHom p A e) γ).val y = p (γ.val y) :=
    (RelGenLoop.map_apply _ γ y).trans (preimageBasedPairHom_fst_apply A e _)
  -- Lift the homotopy `F` of the images from `γ₀` and `γ₁` at its ends, staying at `e` on the
  -- face `{1} × Iᴺ` and on the sides.
  obtain ⟨L, hL, hL₀, hL₁, hLe⟩ := exists_lift_homotopy_of_mem_serreFibrations hp (x₀ := e.val)
    (G₀ := γ₀.val) (G₁ := γ₁.val) (RelGenLoop.mem_iff.1 γ₀.property).2
    (RelGenLoop.mem_iff.1 γ₁.property).2 F.toContinuousMap
    (fun y ↦ (F.apply_zero y).trans (hmap γ₀ y)) (fun y ↦ (F.apply_one y).trans (hmap γ₁ y))
    fun r ↦ (RelGenLoop.mem_iff.1 (F.prop r)).2
  -- On the free face the lift lies over `A`, so its stages are relative cubes.
  refine RelHomotopyGroup.mk_eq_mk.2 <| RelGenLoop.homotopic_iff.2 ⟨{
    toFun := L
    continuous_toFun := L.continuous
    map_zero_left := hL₀
    map_one_left := hL₁
    prop' := fun r ↦ RelGenLoop.mem_iff.2 ⟨fun t ↦ ⟨⟨L (r, 0, t), ?_⟩, rfl⟩, hLe r⟩ }⟩
  have hF := (RelGenLoop.mem_iff.1 (F.prop r)).1 t
  rw [TopPair.range_ofSubset_map] at hF
  rwa [mem_preimage, hL]

/-- **A Serre fibration induces bijections of relative homotopy sets** (Hatcher, Theorem 4.41).
For a Serre fibration `p : E ⟶ B`, `A ⊆ B` and `e ∈ p⁻¹(A)`, the map
`π_{n+1}(E, p⁻¹(A), e) → π_{n+1}(B, A, p e)` induced by `p` is a bijection, where `n` is the
cardinality of `N`. -/
theorem relHomotopyGroup_map_bijective_of_mem_serreFibrations (hp : serreFibrations p)
    {N : Type v} [Finite N] (A : Set B) (e : p ⁻¹' A) :
    Function.Bijective (RelHomotopyGroup.map (N := N) (preimageBasedPairHom p A e)) :=
  ⟨relHomotopyGroup_map_injective_of_mem_serreFibrations hp A e,
    relHomotopyGroup_map_surjective_of_mem_serreFibrations hp A e⟩

/-- **A Serre fibration pulls back trivial relative homotopy sets.** If `p : E ⟶ B` is a Serre
fibration, `A ⊆ B` and `e ∈ p⁻¹(A)`, and the relative homotopy set `π_{n+1}(B, A, p e)` is
trivial, then so is `π_{n+1}(E, p⁻¹(A), e)`, where `n` is the cardinality of `N`. -/
theorem subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations (hp : serreFibrations p)
    {N : Type v} [Finite N] {A : Set B} (e : p ⁻¹' A)
    (h : Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset A, ⟨p e, e.property⟩⟩)) :
    Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset (p ⁻¹' A), e⟩) :=
  haveI := h
  (relHomotopyGroup_map_injective_of_mem_serreFibrations hp A e).subsingleton

/-- **A Serre fibration pulls back path-connectedness to a subspace.** If `p : E ⟶ B` is a Serre
fibration and every point of `B` is joined by a path to a point of `A ⊆ B`, then every point of
`E` is joined by a path to a point of `p⁻¹(A)`. -/
theorem exists_joined_preimage_of_mem_serreFibrations (hp : serreFibrations p) {A : Set B}
    (h : ∀ b : B, ∃ a ∈ A, Joined b a) (x : E) : ∃ y ∈ p ⁻¹' A, Joined x y := by
  obtain ⟨a, ha, ⟨γ⟩⟩ := h (p x)
  obtain ⟨Γ, hΓ₀, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp γ
  refine ⟨Γ 1, ?_, ⟨⟨Γ, hΓ₀, rfl⟩⟩⟩
  have hΓ₁ := congrFun hΓ 1
  rw [Function.comp_apply] at hΓ₁
  rw [mem_preimage, hΓ₁, γ.target]
  exact ha

end TopCat

end TauCeti
