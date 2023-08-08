import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Covering
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Topology.UnitInterval
import Coverings.lean3

open Topology Filter unitInterval Bundle Function Set
namespace IsCoveringMap

/-
Notation:
`E` : the covering space of `X`
`F` : the lift of the map `f`
`F₀` : the start of `F`, i.e. `F₀ = F(y, 0)`

`U : ι → Set α` : collection of (open) sets of α
`s ⊆ ⋃ i, U i` : a (possibly infinite) open cover 
`∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i` : existence of finite subcover

`Continuous f` : `f` is globally continuous
`ContinuousAt f a` : `f` is continuous at the point a

`IsCompact (s : Set α)` : the set s is compact in topological space `α`

`Trivialization F proj` : local trivialization of `proj : E → B` with fiber `F`
`IsEvenlyCovered x ι` : `DiscreteTopology ι ∧ ∃ t : Trivialization ι p, x ∈ t.baseSet`
                      : fiber over x has discrete topology & has a local trivialization
`IsCoveringMap (f : E → X)` : `∀ x, IsEvenlyCovered (f x) (f ⁻¹' {x})`

`∀ᶠ y ∈ 𝓝 x, P y` : exists a nbhd `U` of `x` such that `y ∈ U → P y`

Theorems:
`toTrivialization` : gets local trivialization above a point from a covering map
`IsCompact.elim_finite_subcover` : reduces open cover to finite cover

`isCompact_singleton` : set of a single point is compact
`isCompact_prod` : product of compact sets is compact
-/

variable {X E : Type _}
variable [TopologicalSpace X] [TopologicalSpace E]
variable {p : C(E, X)}
variable {Y : Type _} [TopologicalSpace Y]
variable {hp : IsCoveringMap p} (φ : LiftingSetup Y hp)

structure LiftingSetup (Y : Type _) [TopologicalSpace Y] (hp : IsCoveringMap p) where
  f : C(Y × I, X)
  F₀ : C(Y, E)
  f_eq_pF₀ : ∀ y : Y, f (y, 0) = (p ∘ F₀) y

structure TrivializedNbhd (y : Y) (t : I) where
  triv : Trivialization (p ⁻¹' {φ.f (y, t)}) p
  -- U is a nbhd of (y, t) which maps to triv.baseSet
  U : Set (Y × I)
  hU : U ∈ 𝓝 (y, t)

lemma nbhd_in_trivialization (y : Y) (t : I) :
  ∃ triv : Trivialization (p ⁻¹' {φ.f (y, t)}) p, φ.f ⁻¹' triv.baseSet ∈ 𝓝 (y, t) := by
    specialize hp <| φ.f (y, t)
    let triv : Trivialization (p ⁻¹' {φ.f (y, t)}) p := by
      apply IsEvenlyCovered.toTrivialization hp
    use triv 
    rw [mem_nhds_iff]
    use φ.f ⁻¹' triv.baseSet
    constructor
    . rfl
    . constructor
      . exact IsOpen.preimage φ.f.continuous_toFun triv.open_baseSet
      . rw [preimage]
        exact IsEvenlyCovered.mem_toTrivialization_baseSet hp

noncomputable def triv_nbhd (y : Y) (t : I) : TrivializedNbhd φ y t where
  triv := (nbhd_in_trivialization φ y t).choose
  U := φ.f ⁻¹' (nbhd_in_trivialization φ y t).choose.baseSet
  hU := (nbhd_in_trivialization φ y t).choose_spec

theorem existence_of_homotopy_lift : ∃ F : C(Y × I, E), p ∘ F = f ∧ (fun y ↦ F (y, 0)) = F₀ := by
  sorry