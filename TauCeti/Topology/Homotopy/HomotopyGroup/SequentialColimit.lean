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
* `TauCeti.TopCat.homOfLE_induction`: induction principle along transition maps of a sequential
  diagram `F : ℕ ⥤ TopCat`.
* `TauCeti.TopCat.surjective_homotopyGroup_map_ι`,
  `TauCeti.TopCat.injective_homotopyGroup_map_ι`, `TauCeti.TopCat.bijective_homotopyGroup_map_ι`,
  `TauCeti.TopCat.homotopyGroupMulEquivι`, `TauCeti.TopCat.homotopyGroupMulEquivι_apply`:
  stagewise surjectivity, injectivity, and bijectivity on homotopy groups above stage `m`
  descend to the canonical inclusion `c.ι.app m`.
* `TauCeti.TopCat.isNConnected_ι_of_forall_succ`: if every transition map
  `F.obj k ⟶ F.obj (k + 1)` with `m ≤ k` is `d`-connected, then `c.ι.app m : F.obj m ⟶ c.pt`
  is `d`-connected.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open CategoryTheory Limits Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

/-- Induction principle along transition morphisms `F.map (homOfLE hmn)` of a sequential diagram
`F : ℕ ⥤ TopCat` starting from stage `m`. -/
theorem homOfLE_induction {F : ℕ ⥤ TopCat.{u}} (m : ℕ) (P : ∀ ⦃n : ℕ⦄, C(F.obj m, F.obj n) → Prop)
    (hid : P (ContinuousMap.id (F.obj m)))
    (hstep : ∀ ⦃n : ℕ⦄ (hmn : m ≤ n), P (F.map (homOfLE hmn)).hom →
      P ((F.map (homOfLE n.le_succ)).hom.comp (F.map (homOfLE hmn)).hom))
    {n : ℕ} (hmn : m ≤ n) : P (F.map (homOfLE hmn)).hom := by
  induction hmn with
  | refl =>
    have h : (F.map (homOfLE (le_refl m))).hom = ContinuousMap.id (F.obj m) := by
      ext z
      rw [Subsingleton.elim (homOfLE (le_refl m)) (𝟙 m), F.map_id, TopCat.coe_id, id_eq,
        ContinuousMap.id_apply]
    exact h ▸ hid
  | @step k hmk ih =>
    have h : (F.map (homOfLE hmk.step)).hom =
        (F.map (homOfLE k.le_succ)).hom.comp (F.map (homOfLE hmk)).hom := by
      ext z
      rw [ContinuousMap.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp, homOfLE_comp]
    exact h ▸ hstep hmk ih

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
  have hval (r : Ω^ N (F.obj m) x) (z : I^N) :
      ((GenLoop.map (c.ι.app m).hom rfl r : Ω^ N c.pt _) : C(I^N, c.pt)) z =
        c.ι.app n (F.map (homOfLE hmn) (r z)) := by
    rw [_root_.GenLoop.coe_coe, GenLoop.map_apply, hc_w]
  refine ⟨n, hmn, GenLoop.homotopic_of_continuousMap g' (fun z ↦ ?_) (fun z ↦ ?_)
    fun t z hz ↦ ?_⟩
  · apply (hι n).injective
    rw [hcomp, H'.apply_zero z, hval, GenLoop.map_apply]
  · apply (hι n).injective
    rw [hcomp, H'.apply_one z, hval, GenLoop.map_apply]
  · apply (hι n).injective
    rw [hcomp, H'.eq_fst t hz, hval, _root_.GenLoop.boundary p z hz]

end Lift

section HomotopyGroup

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
  (hι : ∀ n, IsEmbedding (c.ι.app n))

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
  have hstep : ∀ ⦃n : ℕ⦄ (hmn : m ≤ n),
      Function.Surjective (HomotopyGroup.map (N := N) (x := x) (F.map (homOfLE hmn)).hom rfl) :=
    fun _ hmn ↦ homOfLE_induction m
      (fun _ f ↦ Function.Surjective (HomotopyGroup.map (N := N) (x := x) f rfl))
      (fun b ↦ ⟨b, HomotopyGroup.map_id_apply b⟩)
      (fun k hmk ih ↦
        HomotopyGroup.map_comp_map (F.map (homOfLE k.le_succ)).hom rfl
          (F.map (homOfLE hmk)).hom rfl ▸ (hsurj k hmk).comp ih) hmn
  intro b
  induction b using Quotient.inductionOn with | h p =>
  obtain ⟨n, hmn, p', hp'⟩ := exists_lift_genLoop_of_le hc hι m x p
  obtain ⟨a, ha⟩ := hstep hmn ⟦p'⟧
  refine ⟨a, ?_⟩
  have h1 : HomotopyGroup.map (c.ι.app m).hom rfl a =
      HomotopyGroup.map (c.ι.app n).hom (by rw [← ConcreteCategory.comp_apply, c.w])
        (HomotopyGroup.map (F.map (homOfLE hmn)).hom rfl a) :=
    (congrFun (homotopyGroup_map_ι_comp_le hmn x) a).symm
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
  have hstep : ∀ ⦃n : ℕ⦄ (hmn : m ≤ n),
      Function.Injective (HomotopyGroup.map (N := N) (x := x) (F.map (homOfLE hmn)).hom rfl) :=
    fun _ hmn ↦ homOfLE_induction m
      (fun _ f ↦ Function.Injective (HomotopyGroup.map (N := N) (x := x) f rfl))
      (fun a b hab ↦ by rwa [HomotopyGroup.map_id_apply, HomotopyGroup.map_id_apply] at hab)
      (fun k hmk ih ↦
        HomotopyGroup.map_comp_map (F.map (homOfLE k.le_succ)).hom rfl
          (F.map (homOfLE hmk)).hom rfl ▸ (hinj k hmk).comp ih) hmn
  intro a b hab
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk] at hab
  obtain ⟨n, hmn, H⟩ := exists_lift_genLoop_homotopic_of_le hc hι m x (Quotient.exact hab)
  exact hstep hmn (Quotient.sound H)

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
    HomotopyGroup N (F.obj m) x ≃* HomotopyGroup N c.pt (dsimp% c.ι.app m x) :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom (c.ι.app m).hom rfl)
    (bijective_homotopyGroup_map_ι hc hι m x hbij)

include hc hι in
/-- `homotopyGroupMulEquivι` acts on homotopy classes by `HomotopyGroup.map`. -/
@[simp]
theorem homotopyGroupMulEquivι_apply {N : Type*} [DecidableEq N] [Nonempty N]
    (m : ℕ) (x : F.obj m)
    (hbij : ∀ (k : ℕ) (hmk : m ≤ k),
      Function.Bijective (HomotopyGroup.map (N := N) (F.map (homOfLE k.le_succ)).hom
        (rfl : F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x) =
          F.map (homOfLE k.le_succ) (F.map (homOfLE hmk) x))))
    (a : HomotopyGroup N (F.obj m) x) :
    homotopyGroupMulEquivι hc hι m x hbij a = HomotopyGroup.map (c.ι.app m).hom rfl a :=
  HomotopyGroup.mapHom_apply (c.ι.app m).hom rfl a

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
    let k := max m n₀
    have hmk : m ≤ k := le_max_left m n₀
    have hn₀ : n₀ ≤ k := le_max_right m n₀
    have hstep : ∀ ⦃n : ℕ⦄ (hmn : m ≤ n), (F.map (homOfLE hmn)).hom.IsNConnected d :=
      fun _ hmn ↦ homOfLE_induction m (fun _ f ↦ f.IsNConnected d)
        (ContinuousMap.IsWeakHomotopyEquivalence.id.isNConnected d)
        (fun j hmj ih ↦ (hconn j hmj).comp ih) hmn
    let z : F.obj k := F.map (homOfLE hn₀) x₀
    obtain ⟨x, hx⟩ := (hstep hmk).exists_joined z
    refine ⟨x, ?_⟩
    have h1 : c.ι.app k (F.map (homOfLE hmk) x) = c.ι.app m x := by
      rw [← ConcreteCategory.comp_apply, c.w]
    have h2 : c.ι.app k z = c.ι.app n₀ x₀ := by
      dsimp [z]
      rw [← ConcreteCategory.comp_apply, c.w]
    rw [← h1, ← h2]
    exact hx.map (c.ι.app k).hom.continuous
  injective k hk x :=
    injective_homotopyGroup_map_ι hc hι m x fun j hmj ↦ (hconn j hmj).injective k hk _
  surjective k hk x :=
    surjective_homotopyGroup_map_ι hc hι m x fun j hmj ↦ (hconn j hmj).surjective k hk _

end HomotopyGroup

end TauCeti.TopCat
