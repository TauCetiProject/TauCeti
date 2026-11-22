/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Compact
public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic
import TauCeti.Topology.Homotopy.GenLoop.Homotopic

/-!
# Homotopy groups and connectivity of sequential colimits in `TopCat`

For a sequential diagram `F : ℕ ⥤ TopCat` of `T1` spaces whose colimit cocone `c` consists of
topological embeddings (for instance, closed embeddings into a sequential colimit along closed
embeddings), every continuous map from a compact space into `c.pt` factors through some finite
stage (`TauCeti.TopCat.exists_lift_of_compactSpace`). Because finite-dimensional cubes `I^N` and
homotopy cylinders `I × I^N` are compact, generalized loops and relative homotopies in `c.pt` lift
to finite stages:

* `TauCeti.TopCat.exists_lift_genLoop_of_le`: every generalized loop at a stage-`m` basepoint
  lifts to a generalized loop in some stage `n ≥ m`.
* `TauCeti.TopCat.exists_lift_genLoop_homotopic_of_le`: two generalized loops in stage `m` that
  become homotopic in `c.pt` are already homotopic in some stage `n ≥ m`.
* `TauCeti.TopCat.surjective_homotopyGroup_map_ι`,
  `TauCeti.TopCat.injective_homotopyGroup_map_ι`, `TauCeti.TopCat.bijective_homotopyGroup_map_ι`,
  `TauCeti.TopCat.homotopyGroupMulEquivι`: stagewise surjectivity, injectivity, and bijectivity
  on homotopy groups above stage `m` descend to the canonical inclusion `c.ι.app m`.
* `TauCeti.TopCat.isNConnected_ι_of_forall_succ`: if every transition map
  `F.obj k ⟶ F.obj (k + 1)` with `m ≤ k` is `d`-connected, then `c.ι.app m : F.obj m ⟶ c.pt`
  is `d`-connected.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open CategoryTheory Limits Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

section Lift

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} [∀ n, T1Space (F.obj n)] (hc : IsColimit c)
  (hι : ∀ n, IsEmbedding (c.ι.app n))

include hc hι in
/-- In a sequential colimit of `T1` spaces along embeddings, every generalized loop at a
basepoint in stage `m` lifts to a generalized loop in some stage `n ≥ m`. -/
theorem exists_lift_genLoop_of_le {N : Type*} (m : ℕ) (x : F.obj m)
    (p : Ω^ N c.pt (c.ι.app m x)) :
    ∃ (n : ℕ) (hmn : m ≤ n) (p' : Ω^ N (F.obj n) (F.map (homOfLE hmn) x)),
      GenLoop.map (c.ι.app n).hom
        (by rw [← ConcreteCategory.comp_apply, c.w]) p' = p := by
  obtain ⟨n₀, g, hg⟩ := exists_lift_of_compactSpace hc hι p.val
  let n := max m n₀
  have hmn : m ≤ n := le_max_left m n₀
  have hn₀ : n₀ ≤ n := le_max_right m n₀
  let g' : C(I^N, F.obj n) := (F.map (homOfLE hn₀)).hom.comp g
  have hcomp : (c.ι.app n).hom.comp g' = p.val := by
    ext t
    calc
      c.ι.app n (F.map (homOfLE hn₀) (g t))
        = c.ι.app n₀ (g t) := by rw [← ConcreteCategory.comp_apply, c.w]
      _ = p t := ContinuousMap.congr_fun hg t
  have hbd : ∀ t ∈ Cube.boundary N, g' t = F.map (homOfLE hmn) x := fun t ht ↦ by
    refine (hι n).injective ?_
    calc
      c.ι.app n (g' t) = p t := ContinuousMap.congr_fun hcomp t
      _ = c.ι.app m x := p.property t ht
      _ = c.ι.app n (F.map (homOfLE hmn) x) := by rw [← ConcreteCategory.comp_apply, c.w]
  refine ⟨n, hmn, ⟨g', hbd⟩, _root_.GenLoop.ext _ _ fun t ↦ ?_⟩
  rw [GenLoop.map_apply]
  exact ContinuousMap.congr_fun hcomp t

include hc hι in
/-- In a sequential colimit of `T1` spaces along embeddings, if two generalized loops in stage `m`
are homotopic in the colimit, then they become homotopic in some stage `n ≥ m`. -/
theorem exists_lift_genLoop_homotopic_of_le {N : Type*} (m : ℕ) (x : F.obj m)
    {p q : Ω^ N (F.obj m) x}
    (H : _root_.GenLoop.Homotopic (GenLoop.map (c.ι.app m).hom rfl p)
      (GenLoop.map (c.ι.app m).hom rfl q)) :
    ∃ (n : ℕ) (hmn : m ≤ n),
      _root_.GenLoop.Homotopic (GenLoop.map (F.map (homOfLE hmn)).hom rfl p)
        (GenLoop.map (F.map (homOfLE hmn)).hom rfl q) := by
  obtain ⟨H'⟩ := H
  obtain ⟨n₀, g, hg⟩ := exists_lift_of_compactSpace hc hι H'.toContinuousMap
  let n := max m n₀
  have hmn : m ≤ n := le_max_left m n₀
  have hn₀ : n₀ ≤ n := le_max_right m n₀
  let g' : C(I × I^N, F.obj n) := (F.map (homOfLE hn₀)).hom.comp g
  have hcomp (t : I) (z : I^N) : c.ι.app n (g' (t, z)) = H' (t, z) := by
    calc
      c.ι.app n (F.map (homOfLE hn₀) (g (t, z)))
        = c.ι.app n₀ (g (t, z)) := by rw [← ConcreteCategory.comp_apply, c.w]
      _ = H' (t, z) := ContinuousMap.congr_fun hg (t, z)
  have hc_w (u : F.obj m) : c.ι.app n (F.map (homOfLE hmn) u) = c.ι.app m u := by
    rw [← ConcreteCategory.comp_apply, c.w]
  refine ⟨n, hmn, GenLoop.homotopic_of_continuousMap g' (fun z ↦ ?_) (fun z ↦ ?_)
    fun t z hz ↦ ?_⟩
  · apply (hι n).injective
    rw [hcomp, H'.apply_zero z, GenLoop.coe_map, ContinuousMap.comp_apply,
      _root_.GenLoop.coe_coe, GenLoop.map_apply]
    exact (hc_w (p z)).symm
  · apply (hι n).injective
    rw [hcomp, H'.apply_one z, GenLoop.coe_map, ContinuousMap.comp_apply,
      _root_.GenLoop.coe_coe, GenLoop.map_apply]
    exact (hc_w (q z)).symm
  · apply (hι n).injective
    rw [hcomp, H'.eq_fst t hz, GenLoop.coe_map, ContinuousMap.comp_apply,
      _root_.GenLoop.coe_coe, _root_.GenLoop.boundary p z hz, hc_w x]

end Lift

section HomotopyGroup

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
  (hι : ∀ n, IsEmbedding (c.ι.app n))

private theorem homotopyGroup_map_comp_le {N : Type*} {m k : ℕ} (hmk : m ≤ k) (x : F.obj m) :
    HomotopyGroup.map (N := N) (x := F.map (homOfLE hmk) x)
          (F.map (homOfLE k.le_succ)).hom rfl ∘
        HomotopyGroup.map (x := x) (F.map (homOfLE hmk)).hom rfl =
      HomotopyGroup.map (x := x) (F.map (homOfLE (hmk.trans k.le_succ))).hom
        (by rw [← ConcreteCategory.comp_apply, ← F.map_comp]; rfl) := by
  refine HomotopyGroup.map_comp_map_of_comp_eq ?_ rfl rfl _
  ext z
  rw [ContinuousMap.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp]
  rfl

private theorem homotopyGroup_map_ι_comp_le {N : Type*} {m n : ℕ} (hmn : m ≤ n) (x : F.obj m) :
    HomotopyGroup.map (N := N) (x := F.map (homOfLE hmn) x) (c.ι.app n).hom
          (by rw [← ConcreteCategory.comp_apply, c.w]) ∘
        HomotopyGroup.map (x := x) (F.map (homOfLE hmn)).hom rfl =
      HomotopyGroup.map (x := x) (c.ι.app m).hom rfl := by
  refine HomotopyGroup.map_comp_map_of_comp_eq ?_ _ rfl rfl
  ext z
  rw [ContinuousMap.comp_apply, ← ConcreteCategory.comp_apply, c.w]

variable [∀ n, T1Space (F.obj n)]

include hc hι in
/-- If every transition map from stage `m` onwards induces a surjection on `π_N` along the orbit
of `x`, then `c.ι.app m` induces a surjection on `π_N` at `x`. -/
theorem surjective_homotopyGroup_map_ι {N : Type*} (m : ℕ) (x : F.obj m)
    (hsurj : ∀ (k : ℕ) (hmk : m ≤ k),
      Function.Surjective (HomotopyGroup.map (N := N) (F.map (homOfLE k.le_succ)).hom
        (rfl : F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x) =
          F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x)))) :
    Function.Surjective (HomotopyGroup.map (N := N) (c.ι.app m).hom rfl (x := x)) := by
  have hstep : ∀ (d : ℕ),
      Function.Surjective (HomotopyGroup.map (N := N) (x := x)
        (F.map (homOfLE (Nat.le_add_right m d))).hom rfl) := by
    intro d
    induction d with
    | zero =>
      intro a
      have hx : ContinuousMap.id (F.obj m) (F.map (homOfLE (Nat.le_add_right m 0)) x) = x := by
        change F.map (𝟙 m) x = x; simp
      have hcomp : (F.map (homOfLE (Nat.le_add_right m 0))).hom.comp
          (ContinuousMap.id (F.obj m)) = ContinuousMap.id (F.obj m) := by
        ext z; change F.map (𝟙 m) z = z; simp
      refine ⟨HomotopyGroup.map (ContinuousMap.id (F.obj m)) hx a, ?_⟩
      exact HomotopyGroup.map_map_of_comp_eq_id (F.map (homOfLE (Nat.le_add_right m 0))).hom
        (ContinuousMap.id (F.obj m)) hx rfl hcomp a
    | succ d ih =>
      have hcomp := (hsurj (m + d) (Nat.le_add_right m d)).comp ih
      rw [homotopyGroup_map_comp_le (F := F) (Nat.le_add_right m d) x] at hcomp
      exact (HomotopyGroup.surjective_map_congr rfl _ rfl).1 hcomp
  intro b
  induction b using Quotient.inductionOn with | h p =>
  obtain ⟨n, hmn, p', hp'⟩ := exists_lift_genLoop_of_le hc hι m x p
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨a, ha⟩ := hstep d ⟦p'⟧
  refine ⟨a, ?_⟩
  have h1 : HomotopyGroup.map (c.ι.app m).hom rfl a =
      HomotopyGroup.map (c.ι.app (m + d)).hom (by rw [← ConcreteCategory.comp_apply, c.w])
        (HomotopyGroup.map (F.map (homOfLE (Nat.le_add_right m d))).hom rfl a) :=
    (congrFun (homotopyGroup_map_ι_comp_le (Nat.le_add_right m d) x) a).symm
  rw [h1, ha, HomotopyGroup.map_mk]
  exact congrArg Quotient.mk' hp'

include hc hι in
/-- If every transition map from stage `m` onwards induces an injection on `π_N` along the orbit
of `x`, then `c.ι.app m` induces an injection on `π_N` at `x`. -/
theorem injective_homotopyGroup_map_ι {N : Type*} (m : ℕ) (x : F.obj m)
    (hinj : ∀ (k : ℕ) (hmk : m ≤ k),
      Function.Injective (HomotopyGroup.map (N := N) (F.map (homOfLE k.le_succ)).hom
        (rfl : F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x) =
          F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x)))) :
    Function.Injective (HomotopyGroup.map (N := N) (c.ι.app m).hom rfl (x := x)) := by
  have hstep : ∀ (d : ℕ),
      Function.Injective (HomotopyGroup.map (N := N) (x := x)
        (F.map (homOfLE (Nat.le_add_right m d))).hom rfl) := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      have hx : F.map (homOfLE (Nat.le_add_right m 0)) x = x := by
        change F.map (𝟙 m) x = x; simp
      have hcomp : (ContinuousMap.id (F.obj m)).comp
          (F.map (homOfLE (Nat.le_add_right m 0))).hom = ContinuousMap.id (F.obj m) := by
        ext z; change F.map (𝟙 m) z = z; simp
      have hab' := congrArg (HomotopyGroup.map (N := N) (ContinuousMap.id (F.obj m)) hx) hab
      rwa [HomotopyGroup.map_map_of_comp_eq_id _ _ rfl hx hcomp a,
        HomotopyGroup.map_map_of_comp_eq_id _ _ rfl hx hcomp b] at hab'
    | succ d ih =>
      have hcomp := (hinj (m + d) (Nat.le_add_right m d)).comp ih
      rw [homotopyGroup_map_comp_le (F := F) (Nat.le_add_right m d) x] at hcomp
      exact (HomotopyGroup.injective_map_congr rfl _ rfl).1 hcomp
  intro a b hab
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk] at hab
  obtain ⟨n, hmn, H⟩ := exists_lift_genLoop_homotopic_of_le hc hι m x (Quotient.exact hab)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact hstep d (Quotient.sound H)

include hc hι in
/-- If every transition map from stage `m` onwards induces a bijection on `π_N` along the orbit
of `x`, then `c.ι.app m` induces a bijection on `π_N` at `x`. -/
theorem bijective_homotopyGroup_map_ι {N : Type*} (m : ℕ) (x : F.obj m)
    (hbij : ∀ (k : ℕ) (hmk : m ≤ k),
      Function.Bijective (HomotopyGroup.map (N := N) (F.map (homOfLE k.le_succ)).hom
        (rfl : F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x) =
          F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x)))) :
    Function.Bijective (HomotopyGroup.map (N := N) (c.ι.app m).hom rfl (x := x)) :=
  ⟨injective_homotopyGroup_map_ι hc hι m x fun k hmk ↦ (hbij k hmk).1,
   surjective_homotopyGroup_map_ι hc hι m x fun k hmk ↦ (hbij k hmk).2⟩

include hc hι in
/-- Positive-dimensional version of `bijective_homotopyGroup_map_ι` as a group isomorphism
`π_N(F.obj m, x) ≃* π_N(c.pt, c.ι.app m x)`. -/
noncomputable def homotopyGroupMulEquivι {N : Type*} [DecidableEq N] [Nonempty N]
    (m : ℕ) (x : F.obj m)
    (hbij : ∀ (k : ℕ) (hmk : m ≤ k),
      Function.Bijective (HomotopyGroup.map (N := N) (F.map (homOfLE k.le_succ)).hom
        (rfl : F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x) =
          F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x)))) :
    HomotopyGroup N (F.obj m) x ≃* HomotopyGroup N c.pt (c.ι.app m x) :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom (c.ι.app m).hom rfl)
    (bijective_homotopyGroup_map_ι hc hι m x hbij)

include hc hι in
/-- In a sequential colimit of `T1` spaces along embeddings, if every transition map from stage
`m` onwards is `d`-connected, then `c.ι.app m : F.obj m ⟶ c.pt` is `d`-connected. -/
theorem isNConnected_ι_of_forall_succ (m d : ℕ)
    (hconn : ∀ (k : ℕ), m ≤ k → (F.map (homOfLE k.le_succ)).hom.IsNConnected d) :
    (c.ι.app m).hom.IsNConnected d where
  exists_joined y := by
    obtain ⟨n₀, x₀, rfl⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) y
    dsimp
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left m n₀)
    have hstep : ∀ (d' : ℕ) (z : F.obj (m + d')),
        ∃ x : F.obj m, Joined (F.map (homOfLE (Nat.le_add_right m d')) x) z := by
      intro d'
      induction d' with
      | zero =>
        intro z
        refine ⟨z, ?_⟩
        change Joined (F.map (𝟙 m) z) z
        simp [Joined.refl]
      | succ d' ih =>
        intro z
        obtain ⟨z', hz'⟩ := (hconn (m + d') (Nat.le_add_right m d')).exists_joined z
        obtain ⟨x, hx⟩ := ih z'
        refine ⟨x, ?_⟩
        have hcomp : F.map (homOfLE (Nat.le_add_right m (d' + 1))) x =
            F.map (homOfLE (m + d').le_succ)
              (F.map (homOfLE (Nat.le_add_right m d')) x) := by
          rw [← ConcreteCategory.comp_apply, ← F.map_comp]
          rfl
        rw [hcomp]
        exact (hx.map (F.map (homOfLE (m + d').le_succ)).hom.continuous).trans hz'
    let z : F.obj (m + k) := F.map (homOfLE (hk ▸ le_max_right m n₀)) x₀
    obtain ⟨x, hx⟩ := hstep k z
    refine ⟨x, ?_⟩
    have h1 : c.ι.app (m + k) (F.map (homOfLE (Nat.le_add_right m k)) x) = c.ι.app m x := by
      rw [← ConcreteCategory.comp_apply, c.w]
    have h2 : c.ι.app (m + k) z = c.ι.app n₀ x₀ := by
      dsimp [z]
      rw [← ConcreteCategory.comp_apply, c.w]
    rw [← h1, ← h2]
    exact hx.map (c.ι.app (m + k)).hom.continuous
  injective k hk x :=
    injective_homotopyGroup_map_ι hc hι m x fun j hmj ↦ (hconn j hmj).injective k hk _
  surjective k hk x :=
    surjective_homotopyGroup_map_ι hc hι m x fun j hmj ↦ (hconn j hmj).surjective k hk _

end HomotopyGroup

end TauCeti.TopCat
