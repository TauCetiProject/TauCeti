/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.NTQ.Tower
public import TauCeti.GroupTheory.LimitGroup.NTQ.Specialization
public import TauCeti.GroupTheory.GroupAlgGeom.SolutionImage
public import TauCeti.GroupTheory.GroupAlgGeom.Irreducible.FreeGroup
public import TauCeti.GroupTheory.GroupAlgGeom.FreeDiscrimination
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.FreeProduct
import TauCeti.GroupTheory.NoncommPiCoprod
import TauCeti.Topology.NoetherianSpace.Decomposition

/-!
# Finite covers of solution sets by normalized towers

Let `S` be a system of equations over a group `G` in the variables `X`, and `P` a set of its
solutions. A *tower cover* of `P` is a finite family of normalized towers `T_j` over `G` together
with `G`-homomorphisms `θ_j : G_{R(S)} → T_j` from the coordinate group of `S`, such that every
point of `P` is `ψ ∘ p_j` for some `j` and some homomorphism `ψ : T_j → G` over `G`, where
`p_j = θ_j ∘ (x ↦ x)` is the tuple of images of the variables. Since `θ_j` is defined on the
coordinate group, every such `ψ ∘ p_j` is a solution of `S`; so a tower cover of `P = V(S)` writes
`V(S)` as the finite union of the images `{ψ ∘ p_j}`. All homomorphisms of the towers over `G` are
used, not only compositions of their level retractions.

The images of the `T_j` that are discriminated by `G` are irreducible; the radical of `S` is the
intersection of the kernels of the evaluations at the `p_j`; and if `V(S)` is irreducible, one of
the images is dense in `V(S)`, and the corresponding `θ_j` is injective. So a tower cover of an
irreducible algebraic set embeds its coordinate group, over `G`, in a normalized tower.

## Main definitions

* `TauCeti.LimitGroup.NTQ.TowerCover S P`: a finite cover of `P` by normalized towers.
* `TauCeti.LimitGroup.NTQ.TowerCover.ofBijective`: the one-tower cover given by an isomorphism of
  the coordinate group with a tower; `TauCeti.LimitGroup.NTQ.TowerCover.mono`: restriction to a
  subset.

## Main results

* `TauCeti.LimitGroup.NTQ.TowerCover.V_eq_iUnion`: a tower cover of `V(S)` writes it as the union
  of the images.
* `TauCeti.LimitGroup.NTQ.TowerCover.n_eq_zero_iff`: a tower cover of `V(S)` is empty exactly when
  `S` has no solution.
* `TauCeti.LimitGroup.NTQ.TowerCover.isIrreducible_range`: images of discriminated towers are
  irreducible.
* `TauCeti.LimitGroup.NTQ.TowerCover.Rad_eq_iInf_ker`: the radical of `S` is the intersection of
  the kernels of the evaluations at the `p_j`.
* `TauCeti.LimitGroup.NTQ.TowerCover.exists_closure_range_eq`,
  `TauCeti.LimitGroup.NTQ.TowerCover.injective_hom_of_closure_eq`: over an irreducible `V(S)`, some
  image is dense, and its `θ_j` is injective.
* Examples: `TauCeti.LimitGroup.NTQ.exists_bijective_gHom_coordGroup_empty` (the empty system,
  whose coordinate group is `F[X]`); `TauCeti.LimitGroup.NTQ.V_commutatorPair_eq_union_range`,
  `TauCeti.LimitGroup.NTQ.exists_gHom_commutatorPair_free`,
  `TauCeti.LimitGroup.NTQ.exists_gHom_commutatorPair_abelian` and
  `TauCeti.LimitGroup.NTQ.notMem_range_abelian_commutatorPair` (the two towers of
  `[u, v] = [u, x] = 1`); covers of `[x, a] = 1` and of `⟨a⟩ ∪ ⟨b⟩` by centralizer towers; and
  `TauCeti.LimitGroup.NTQ.not_exists_injective_gHom_unionEquations` (the coordinate group of
  `⟨a⟩ ∪ ⟨b⟩` embeds in no discriminated group).

## References

* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §0, Theorems 2–3.
* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.6, Theorem 6.
-/

public section

open Monoid.Coprod TauCeti.GroupAlgGeom FreeGroup Group
open scoped commutatorElement

universe u w

namespace TauCeti.LimitGroup.NTQ

variable {G : Type u} [Group G] {X : Type w}

/-- A *tower cover* of a set `P` of solutions of a system `S` over `G`: finitely many normalized
towers over `G`, each with a `G`-homomorphism from the coordinate group of `S`, such that every
point of `P` is the composite of the images of the variables with a homomorphism of one of the
towers to `G` over `G`. The images need not be irreducible; they are when the towers are
discriminated by `G` (`TauCeti.LimitGroup.NTQ.TowerCover.isIrreducible_range`). -/
structure TowerCover (S : Set (GX G X)) (P : Set (X → G)) where
  /-- The number of towers. -/
  n : ℕ
  /-- The top carrier of the `j`-th tower. -/
  carrier : Fin n → Type u
  /-- The group structure of the carriers. -/
  instGroup : ∀ j, Group (carrier j)
  /-- The coefficient homomorphism of the `j`-th tower. -/
  coeff : ∀ j, G →* carrier j
  /-- The `j`-th tower. -/
  tower : ∀ j, Tower G (carrier j) (coeff j)
  /-- The homomorphism `θ_j` from the coordinate group of `S` to the `j`-th carrier. -/
  hom : ∀ j, GHom (CoordGroup.coeff (MonoidHom.id G) S) (coeff j)
  /-- Every point of `P` factors through one of the towers. -/
  subset_iUnion : P ⊆ ⋃ j, Set.range fun ψ : GHom (coeff j) (MonoidHom.id G) ↦
    ⇑ψ ∘ ⇑(hom j) ∘ CoordGroup.genericPoint (MonoidHom.id G) S

attribute [instance] TowerCover.instGroup

namespace TowerCover

variable {S : Set (GX G X)} {P : Set (X → G)}

/-- The tuple `p_j` of the images of the variables in the `j`-th carrier. -/
def point (c : TowerCover S P) (j : Fin c.n) : X → c.carrier j :=
  ⇑(c.hom j) ∘ CoordGroup.genericPoint (MonoidHom.id G) S

theorem point_def (c : TowerCover S P) (j : Fin c.n) :
    c.point j = ⇑(c.hom j) ∘ CoordGroup.genericPoint (MonoidHom.id G) S := (rfl)

/-- Evaluating an equation at `p_j` gives the image under `θ_j` of its class in the coordinate
group. -/
@[simp]
theorem eval_point (c : TowerCover S P) (j : Fin c.n) (w : GX G X) :
    eval (c.coeff j) (c.point j) w = c.hom j (w : CoordGroup (MonoidHom.id G) S) := by
  rw [point_def, ← map_eval, CoordGroup.eval_genericPoint]

/-- The points `ψ ∘ p_j` are solutions of `S`. -/
theorem range_subset_V (c : TowerCover S P) (j : Fin c.n) :
    (Set.range fun ψ : GHom (c.coeff j) (MonoidHom.id G) ↦ ⇑ψ ∘ c.point j) ⊆
      V (MonoidHom.id G) S := by
  rintro _ ⟨ψ, rfl⟩
  have h := (ψ.comp (c.hom j)).comp_mem_V (CoordGroup.genericPoint_mem_V S)
  rwa [GHom.coe_comp, Function.comp_assoc, ← point_def] at h

/-- A tower cover of `V(S)` writes `V(S)` as the union of the images of its towers. -/
theorem V_eq_iUnion (c : TowerCover S (V (MonoidHom.id G) S)) :
    V (MonoidHom.id G) S = ⋃ j, Set.range fun ψ : GHom (c.coeff j) (MonoidHom.id G) ↦
      ⇑ψ ∘ c.point j :=
  c.subset_iUnion.antisymm (Set.iUnion_subset c.range_subset_V)

/-- A tower cover of `V(S)` has no tower exactly when `S` has no solution: every tower has a
homomorphism to `G` over `G`, its retraction. -/
theorem n_eq_zero_iff (c : TowerCover S (V (MonoidHom.id G) S)) :
    c.n = 0 ↔ V (MonoidHom.id G) S = ∅ := by
  refine ⟨fun h ↦ Set.subset_empty_iff.1 (c.subset_iUnion.trans
    (Set.iUnion_subset fun j ↦ (Fin.cast h j).elim0)), fun h ↦ Nat.eq_zero_of_not_pos fun hn ↦ ?_⟩
  -- The retraction of a tower gives a solution.
  exact Set.eq_empty_iff_forall_notMem.1 h _
    (c.range_subset_V ⟨0, hn⟩ ⟨(c.tower _).retractionGHom, rfl⟩)

/-- The image of a tower discriminated by `G` is irreducible in the Zariski topology. -/
theorem isIrreducible_range (c : TowerCover S P) (j : Fin c.n)
    (h : IsDiscriminatedBy (c.coeff j) (MonoidHom.id G)) :
    @IsIrreducible (X → G) (zariskiTopology (MonoidHom.id G) X)
      (Set.range fun ψ : GHom (c.coeff j) (MonoidHom.id G) ↦ ⇑ψ ∘ c.point j) :=
  h.isIrreducible_range_comp (c.point j)

private theorem mem_I_range (c : TowerCover S P) {j : Fin c.n} {w : GX G X}
    (hw : c.hom j (w : CoordGroup (MonoidHom.id G) S) = 1) :
    w ∈ I (MonoidHom.id G)
      (Set.range fun ψ : GHom (c.coeff j) (MonoidHom.id G) ↦ ⇑ψ ∘ c.point j) := by
  refine mem_I.2 ?_
  rintro _ ⟨ψ, rfl⟩
  rw [← map_eval, eval_point, hw, _root_.map_one]

/-- The radical of `S` is the intersection of the kernels of the evaluations `G[X] → T_j` at the
tuples `p_j` of a tower cover of `V(S)`: a word vanishing at every `p_j` vanishes on every image,
and a word of the radical vanishes at `p_j` since `θ_j` is defined on the coordinate group. -/
theorem Rad_eq_iInf_ker (c : TowerCover S (V (MonoidHom.id G) S)) :
    Rad (MonoidHom.id G) S = ⨅ j, (eval (c.coeff j) (c.point j)).ker := by
  refine le_antisymm (le_iInf fun j w hw ↦ ?_) fun w hw ↦ ?_
  · rw [MonoidHom.mem_ker, eval_point, (QuotientGroup.eq_one_iff w).2 hw, _root_.map_one]
  · rw [Rad_def, c.V_eq_iUnion, I_iUnion]
    exact Subgroup.mem_iInf.2 fun j ↦ c.mem_I_range
      ((c.eval_point j w).symm.trans (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 hw j)))

/-- If `V(S)` is irreducible, the image of some tower of a tower cover of `V(S)` is dense in
`V(S)`. -/
theorem exists_closure_range_eq (c : TowerCover S (V (MonoidHom.id G) S))
    (hS : @IsIrreducible (X → G) (zariskiTopology (MonoidHom.id G) X) (V (MonoidHom.id G) S)) :
    ∃ j, @closure (X → G) (zariskiTopology (MonoidHom.id G) X)
      (Set.range fun ψ : GHom (c.coeff j) (MonoidHom.id G) ↦ ⇑ψ ∘ c.point j) =
        V (MonoidHom.id G) S := by
  let := zariskiTopology (MonoidHom.id G) X
  -- The closures of the finitely many images are closed and cover `V(S)`.
  obtain ⟨j, hj⟩ := hS.exists_subset_of_subset_iUnion (fun _ ↦ isClosed_closure)
    (c.V_eq_iUnion.le.trans (Set.iUnion_mono fun _ ↦ subset_closure))
  exact ⟨j, (closure_minimal (c.range_subset_V j) (isClosed_V S)).antisymm hj⟩

/-- If the image of the `j`-th tower is dense in `V(S)`, then `θ_j` is injective: an element of
the coordinate group killed by `θ_j` is a word vanishing on that image, hence on `V(S)`. -/
theorem injective_hom_of_closure_eq (c : TowerCover S P) {j : Fin c.n}
    (h : @closure (X → G) (zariskiTopology (MonoidHom.id G) X)
      (Set.range fun ψ : GHom (c.coeff j) (MonoidHom.id G) ↦ ⇑ψ ∘ c.point j) =
        V (MonoidHom.id G) S) : Function.Injective (c.hom j) := by
  let := zariskiTopology (MonoidHom.id G) X
  refine (injective_iff_map_eq_one (c.hom j)).2 fun q hq ↦ ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  refine (QuotientGroup.eq_one_iff w).2 (mem_Rad.2 fun v hv ↦ ?_)
  -- The closure of the image lies in the algebraic set of the equations vanishing on it.
  have hv' : v ∈ V (MonoidHom.id G) (I (MonoidHom.id G)
      (Set.range fun ψ : GHom (c.coeff j) (MonoidHom.id G) ↦ ⇑ψ ∘ c.point j)) :=
    closure_minimal (subset_V_I _) (isClosed_V _) (h.symm ▸ hv)
  exact mem_V.1 hv' w (c.mem_I_range hq)

/-- A tower cover of `P` is a tower cover of every subset of `P`. -/
def mono (c : TowerCover S P) {P' : Set (X → G)} (h : P' ⊆ P) : TowerCover S P' where
  n := c.n
  carrier := c.carrier
  instGroup := c.instGroup
  coeff := c.coeff
  tower := c.tower
  hom := c.hom
  subset_iUnion := h.trans c.subset_iUnion

/-- The tower cover of `V(S)` with one tower, given by an isomorphism of the coordinate group of
`S` with the top carrier of a tower. -/
noncomputable def ofBijective {T : Type u} [Group T] {ι : G →* T} (t : Tower G T ι)
    (θ : GHom (CoordGroup.coeff (MonoidHom.id G) S) ι) (hθ : Function.Bijective θ) :
    TowerCover S (V (MonoidHom.id G) S) where
  n := 1
  carrier _ := T
  instGroup _ := inferInstance
  coeff _ := ι
  tower _ := t
  hom _ := θ
  subset_iUnion v hv := Set.mem_iUnion.2
    ⟨0, (CoordGroup.evalGHom v hv).comp (θ.symmOfBijective hθ), funext fun x ↦ by simp⟩

end TowerCover

/-! ### Examples -/

private theorem exists_gHom_coordGroup_of_isSeparatedBy {K : Type*} [Group K] {κ : G →* K}
    (h : IsSeparatedBy κ (MonoidHom.id G)) {S : Set (GX G X)} {p : X → K} (hp : p ∈ V κ S) :
    ∃ θ : GHom (CoordGroup.coeff (MonoidHom.id G) S) κ,
      ⇑θ ∘ CoordGroup.genericPoint (MonoidHom.id G) S = p := by
  -- The radical of `S` vanishes on the points `ψ ∘ p`, hence at `p`.
  have hRad : Rad (MonoidHom.id G) S ≤ (eval κ p).ker := by
    rw [Rad_def, ← h.I_range_comp_eq_ker_eval]
    exact I_antitone _ (Set.range_subset_iff.2 fun ψ : GHom κ (MonoidHom.id G) ↦ ψ.comp_mem_V hp)
  refine ⟨⟨QuotientGroup.lift _ (eval κ p) hRad, fun g ↦ by simp⟩, funext fun x ↦ ?_⟩
  simp [CoordGroup.genericPoint_apply]

/-- Over a nonabelian free group `F`, the coordinate group of the empty system in the variables
`X` is the free `F`-group `F[X] = F ∗ F(X)`, the variables going to themselves. -/
theorem exists_bijective_gHom_coordGroup_empty {F : Type u} [Group F] [IsFreeGroup F]
    (hF : ¬IsMulCommutative F) (X : Type w) :
    ∃ θ : GHom (CoordGroup.coeff (MonoidHom.id F) (∅ : Set (GX F X))) (inl : F →* GX F X),
      Function.Bijective θ ∧
        ⇑θ ∘ CoordGroup.genericPoint (MonoidHom.id F) ∅ = fun x ↦ inr (FreeGroup.of x) := by
  -- `F[X]` is separated by `F`, so evaluation at the variables is defined on `F_{R(∅)}`, where
  -- it sends the class of each `w` to `w`.
  obtain ⟨θ, hθ⟩ := exists_gHom_coordGroup_of_isSeparatedBy (S := ∅)
    (GX.isDiscriminatedBy_of_isFreeGroup hF).isSeparatedBy (p := fun x ↦ inr (of x)) (by simp)
  have hθw (w : GX F X) : θ w = w := by
    simpa [hθ] using map_eval θ (v := CoordGroup.genericPoint (MonoidHom.id F) ∅) w
  refine ⟨θ, ⟨(injective_iff_map_eq_one θ).2 fun q hq ↦ ?_, fun w ↦ ⟨w, hθw w⟩⟩, hθ⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  rw [hθw] at hq
  rw [hq, QuotientGroup.mk_one]

/-- The one-level free tower `F[X]` covers the empty system, with the identity word map. -/
noncomputable example {F : Type u} [Group F] [IsFreeGroup F] (hF : ¬IsMulCommutative F) (X : Type u)
    [Finite X] : TowerCover (∅ : Set (GX F X)) (V (MonoidHom.id F) ∅) :=
  TowerCover.ofBijective (Tower.single (.free X))
    (exists_bijective_gHom_coordGroup_empty hF X).choose
    (exists_bijective_gHom_coordGroup_empty hF X).choose_spec.1

/-- Over `F(α)`, the equation `[x, a] = 1` for a basis letter `a` is covered by the admissible
full-centralizer tower `F(a, ℤ)`, the variable going to the new letter. -/
noncomputable example {α : Type u} (a : α) :
    let w : GX (FreeGroup α) Unit :=
      ⁅(inr (of ()) : GX (FreeGroup α) Unit), (inl (of a) : GX (FreeGroup α) Unit)⁆
    TowerCover {w} (V (MonoidHom.id (FreeGroup α)) {w}) :=
  TowerCover.ofBijective
    (Tower.single
      (.centralizer (of a) {of a} 1 (isAdmissibleCentralizerLevel_freeGroup_of a one_pos)))
    (exists_bijective_gHom_coordGroup_centralizerExt a).choose
    (exists_bijective_gHom_coordGroup_centralizerExt a).choose_spec.1

/-- Over a commutative transitive group `G`, the solutions of `[u, v] = [u, x] = 1` are the images,
under the homomorphisms over `G` to `G`, of two tuples: `(1, v, x)` in `G ∗ F(v, x)`, the carrier
of a free level, whose image is the solutions with `u = 1`, and `(u, v, x)` in `G ∗ ℤ³`, the
carrier of an abelian level, whose image is the pairwise commuting triples. -/
theorem V_commutatorPair_eq_union_range (hG : IsCommTransitive G) :
    V (MonoidHom.id G) (commutatorPair G) =
      (Set.range fun ψ : GHom (inl : G →* GX G (Fin 2)) (MonoidHom.id G) ↦
        ⇑ψ ∘ ![1, inr (of 0), inr (of 1)]) ∪
      Set.range fun ψ : GHom (inl : G →* Monoid.Coprod G (Fin 3 → Multiplicative ℤ))
        (MonoidHom.id G) ↦ ⇑ψ ∘ fun i ↦ inr (Pi.mulSingle i (Multiplicative.ofAdd 1)) := by
  refine Set.Subset.antisymm (fun v hv ↦ ?_) (Set.union_subset ?_ ?_)
  · rw [V_commutatorPair_eq_union hG] at hv
    rcases hv with hv | hv
    · -- `u = 1`: the free level with `v` and `x` as the images of its letters.
      have hv0 : v 0 = 1 := by simpa using hv
      refine Or.inl ⟨evalGHom _ ![v 1, v 2], funext fun i ↦ ?_⟩
      fin_cases i <;> simp [hv0]
    · -- `u`, `v`, `x` commute pairwise: the abelian level, `ℤ³` going to `⟨u, v, x⟩`.
      simp only [mem_V, Set.forall_mem_insert] at hv
      have h12 : Commute (v 1) (v 2) := by simpa [commutatorElement_eq_one_iff_commute] using hv.1
      obtain ⟨h01, h02⟩ := mem_V_commutatorPair.1 (mem_V.2 hv.2)
      have hτ : ∀ i j, Commute (v i) (v j) := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [h01, h02, h12, h01.symm, h02.symm, h12.symm]
      refine Or.inr ⟨⟨lift (MonoidHom.id G) (zpowersPiHom v hτ), lift_apply_inl _ _⟩,
        funext fun i ↦ ?_⟩
      simp
  · rintro _ ⟨ψ, rfl⟩
    exact ψ.comp_mem_V (by simp)
  · rintro _ ⟨ψ, rfl⟩
    refine ψ.comp_mem_V (mem_V_commutatorPair.2 ⟨?_, ?_⟩) <;>
      exact ((Commute.all _ _).map inr)

/-- Over a nonabelian free group `F`, the word map `(u, v, x) ↦ (1, v, x)` induces an
`F`-homomorphism from the coordinate group of `[u, v] = [u, x] = 1` to the free level
`F ∗ F(v, x)`. -/
theorem exists_gHom_commutatorPair_free {F : Type u} [Group F] [IsFreeGroup F]
    (hF : ¬IsMulCommutative F) :
    ∃ θ : GHom (CoordGroup.coeff (MonoidHom.id F) (commutatorPair F)) (inl : F →* GX F (Fin 2)),
      ⇑θ ∘ CoordGroup.genericPoint (MonoidHom.id F) (commutatorPair F) =
        ![1, inr (of 0), inr (of 1)] :=
  exists_gHom_coordGroup_of_isSeparatedBy (GX.isDiscriminatedBy_of_isFreeGroup hF).isSeparatedBy
    (by simp)

/-- Over a nonabelian free group `F`, the word map `(u, v, x) ↦ (u, v, x)` induces an
`F`-homomorphism from the coordinate group of `[u, v] = [u, x] = 1` to the abelian level
`F ∗ ℤ³`. -/
theorem exists_gHom_commutatorPair_abelian {F : Type u} [Group F] [IsFreeGroup F]
    (hF : ¬IsMulCommutative F) :
    ∃ θ : GHom (CoordGroup.coeff (MonoidHom.id F) (commutatorPair F))
        (inl : F →* Monoid.Coprod F (Fin 3 → Multiplicative ℤ)),
      ⇑θ ∘ CoordGroup.genericPoint (MonoidHom.id F) (commutatorPair F) =
        fun i : Fin 3 ↦ inr (Pi.mulSingle i (Multiplicative.ofAdd 1)) := by
  -- `F ∗ ℤ³` embeds over `F` in an ICE group over `F`, which is discriminated by `F`.
  obtain ⟨E, _, j, c, f, hf⟩ :=
    exists_ice_embedding_coprod_pi (isFullyResiduallyFree_of_isFreeGroup (G := F)) hF 3
  exact exists_gHom_coordGroup_of_isSeparatedBy
    ((c.isDiscriminatedBy isFullyResiduallyFree_of_isFreeGroup).of_injective f hf).isSeparatedBy
    (mem_V_commutatorPair.2 ⟨(Commute.all _ _).map inr, (Commute.all _ _).map inr⟩)

/-- Over `F(α)`, for distinct basis letters `a`, `b`, the solution `(u, v, x) = (1, a, b)` of
`[u, v] = [u, x] = 1` is not in the image of the abelian level `F ∗ ℤ³`, whose points are pairwise
commuting triples. -/
theorem notMem_range_abelian_commutatorPair {α : Type u} {a b : α} (hab : a ≠ b) :
    ![1, of a, of b] ∉ Set.range fun ψ : GHom (inl : FreeGroup α →*
        Monoid.Coprod (FreeGroup α) (Fin 3 → Multiplicative ℤ)) (MonoidHom.id (FreeGroup α)) ↦
      ⇑ψ ∘ fun i ↦ inr (Pi.mulSingle i (Multiplicative.ofAdd 1)) := by
  rintro ⟨ψ, hψ⟩
  -- The images of two generators of `ℤ³` commute, while `a` and `b` do not.
  refine hab (FreeGroup.eq_of_commute_of_of ?_)
  have h1 := congrFun hψ 1
  have h2 := congrFun hψ 2
  simp only [Function.comp_apply] at h1 h2
  simpa [h1, h2] using ((Commute.all (Pi.mulSingle (1 : Fin 3) (Multiplicative.ofAdd (1 : ℤ)))
    (Pi.mulSingle 2 (Multiplicative.ofAdd 1))).map
      (inr : (Fin 3 → Multiplicative ℤ) →* Monoid.Coprod (FreeGroup α) _)).map ψ

/-- Over `F(α)`, the union `⟨a⟩ ∪ ⟨b⟩` of the centralizers of two basis letters, the solutions of
the equations `[[x, a], g [x, b] g⁻¹] = 1` for `g ∈ F(α)`, is covered by the two admissible
full-centralizer towers `F(a, ℤ)` and `F(b, ℤ)`, the variable going to the new letter in both. -/
noncomputable example {α : Type u} (a b : α) :
    let S : Set (GX (FreeGroup α) Unit) :=
      unionEquations {⁅(inr (of ()) : GX (FreeGroup α) Unit), (inl (of a) : GX (FreeGroup α) Unit)⁆}
        {⁅(inr (of ()) : GX (FreeGroup α) Unit), (inl (of b) : GX (FreeGroup α) Unit)⁆}
    TowerCover S (V (MonoidHom.id (FreeGroup α)) S) := by
  intro S
  let c : Fin 2 → α := ![a, b]
  -- The new letter `t` of `F(c j, ℤ)` commutes with `c j`, so it solves the union equations.
  have hθ (j : Fin 2) : ∃ θ : GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup α)) S)
      (CentralizerExt.of : FreeGroup α →* CentralizerExt (of (c j)) 1),
      ⇑θ ∘ CoordGroup.genericPoint (MonoidHom.id (FreeGroup α)) S =
        fun _ ↦ CentralizerExt.t 0 := by
    have ht : (fun _ ↦ CentralizerExt.t 0) ∈ V (CentralizerExt.of : FreeGroup α →*
        CentralizerExt (of (c j)) 1)
          {⁅(inr (of ()) : GX (FreeGroup α) Unit), (inl (of (c j)) : GX (FreeGroup α) Unit)⁆} := by
      simpa [commutatorElement_eq_one_iff_commute] using
        (CentralizerExt.commute_of_t (Subgroup.mem_centralizer_singleton_iff.2 rfl) 0).symm
    refine exists_gHom_coordGroup_of_isSeparatedBy (CentralizerExt.isDiscriminatedBy
      IsFreeGroup.isBP IsFreeGroup.isCSA (of_ne_one _)).isSeparatedBy
      (union_subset_V_unionEquations _ _ ?_)
    fin_cases j
    exacts [Or.inl ht, Or.inr ht]
  choose θ hθ using hθ
  refine ⟨2, fun j ↦ CentralizerExt (of (c j)) 1, fun _ ↦ inferInstance, fun _ ↦ CentralizerExt.of,
    fun j ↦ .single (.centralizer _ _ 1 (isAdmissibleCentralizerLevel_freeGroup_of (c j) one_pos)),
    θ, fun v hv ↦ ?_⟩
  -- A point with `x = (c j) ^ k` is the image of the new letter under `t ↦ (c j) ^ k`.
  rw [V_unionEquations_commutatorElement_of] at hv
  obtain ⟨j, k, hk⟩ : ∃ j k, of (c j) ^ k = v () :=
    hv.elim (fun ⟨k, hk⟩ ↦ ⟨0, k, hk⟩) fun ⟨k, hk⟩ ↦ ⟨1, k, hk⟩
  refine Set.mem_iUnion.2 ⟨j, ⟨CentralizerExt.lift (MonoidHom.id _) (fun _ ↦ of (c j) ^ k)
    (fun _ _ ↦ .refl _) fun _ hx _ ↦
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 hx) k,
    CentralizerExt.lift_of _ _ _ _⟩, ?_⟩
  rw [hθ j]
  funext
  simp [hk]

/-- Over `F(α)`, for distinct basis letters `a`, `b` and a variable `x` among the variables `X`,
the coordinate group of `⟨a⟩ ∪ ⟨b⟩` (in the `x`-coordinate) embeds, over `F(α)`, in no group
discriminated by `F(α)`, for instance in no normalized tower over `F(α)` discriminated by `F(α)`. -/
theorem not_exists_injective_gHom_unionEquations {α : Type u} {X : Type w} (x : X) {a b : α}
    (hab : a ≠ b) :
    ¬∃ (T : Type*) (_ : Group T) (ι : FreeGroup α →* T)
      (_ : IsDiscriminatedBy ι (MonoidHom.id (FreeGroup α)))
      (θ : GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup α))
        (unionEquations {⁅(inr (of x) : GX (FreeGroup α) X), (inl (of a) : GX (FreeGroup α) X)⁆}
          {⁅(inr (of x) : GX (FreeGroup α) X), (inl (of b) : GX (FreeGroup α) X)⁆})) ι),
      Function.Injective θ := by
  rintro ⟨T, _, ι, hι, θ, hθ⟩
  exact not_isDiscriminatedBy_coordGroup_unionEquations_commutatorElement_of x hab
    (hι.of_injective θ hθ)

end TauCeti.LimitGroup.NTQ
